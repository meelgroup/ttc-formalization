import Ttc.Volume.CVSequentialDependence
import Arlib.MarkovChains.Continuous.HitAndRunMixing

/-!
# Exceptional-event transfer for `NuIndep`

Conditioning an execution on a high-probability good event changes its law in total
variation by at most the failure probability.  This file records the corresponding
stability theorem for the event-form dependence coefficient.  It is deliberately a
law-level statement: no warmness conclusion is inferred from total variation.
-/

namespace Ttc.CVExceptionalDependence

open MeasureTheory ProbabilityTheory Set
open Arlib Arlib.GaussianCooling Arlib.MarkovChains
open scoped ENNReal

/-- Moving the underlying probability law by TV distance `delta` increases the
`NuIndep` coefficient by at most `3 * delta`: one copy for the joint event and
two copies for the product of its marginals. -/
theorem nuIndep_of_tvLe_measure
    {Ω A B : Type*} [MeasurableSpace Ω] [MeasurableSpace A] [MeasurableSpace B]
    {μ ν : Measure Ω} [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {X : Ω → A} {Y : Ω → B} (hX : Measurable X) (hY : Measurable Y)
    {eps : Real} {delta : ENNReal} (hdelta : delta ≠ ⊤)
    (htv : TVLe μ ν delta) (hindep : NuIndep ν X Y eps) :
    NuIndep μ X Y (eps + 3 * delta.toReal) := by
  intro S T hS hT
  have hXS : MeasurableSet (X ⁻¹' S) := hX hS
  have hYT : MeasurableSet (Y ⁻¹' T) := hY hT
  have hJ : MeasurableSet (X ⁻¹' S ∩ Y ⁻¹' T) := hXS.inter hYT
  have hdJ := htv.abs_measureReal_sub_le hdelta hJ
  have hdX := htv.abs_measureReal_sub_le hdelta hXS
  have hdY := htv.abs_measureReal_sub_le hdelta hYT
  have hμX0 : 0 ≤ μ.real (X ⁻¹' S) := measureReal_nonneg
  have hμX1 : μ.real (X ⁻¹' S) ≤ 1 := by
    rw [← probReal_univ (μ := μ)]
    exact measureReal_mono (Set.subset_univ _) (measure_ne_top μ _)
  have hμY0 : 0 ≤ μ.real (Y ⁻¹' T) := measureReal_nonneg
  have hμY1 : μ.real (Y ⁻¹' T) ≤ 1 := by
    rw [← probReal_univ (μ := μ)]
    exact measureReal_mono (Set.subset_univ _) (measure_ne_top μ _)
  have hνX0 : 0 ≤ ν.real (X ⁻¹' S) := measureReal_nonneg
  have hνX1 : ν.real (X ⁻¹' S) ≤ 1 := by
    rw [← probReal_univ (μ := ν)]
    exact measureReal_mono (Set.subset_univ _) (measure_ne_top ν _)
  have hνY0 : 0 ≤ ν.real (Y ⁻¹' T) := measureReal_nonneg
  have hνY1 : ν.real (Y ⁻¹' T) ≤ 1 := by
    rw [← probReal_univ (μ := ν)]
    exact measureReal_mono (Set.subset_univ _) (measure_ne_top ν _)
  have hprod :
      |ν.real (X ⁻¹' S) * ν.real (Y ⁻¹' T) -
          μ.real (X ⁻¹' S) * μ.real (Y ⁻¹' T)| ≤
        2 * delta.toReal := by
    calc
      |ν.real (X ⁻¹' S) * ν.real (Y ⁻¹' T) -
          μ.real (X ⁻¹' S) * μ.real (Y ⁻¹' T)| =
          |(ν.real (X ⁻¹' S) - μ.real (X ⁻¹' S)) * ν.real (Y ⁻¹' T) +
            μ.real (X ⁻¹' S) *
              (ν.real (Y ⁻¹' T) - μ.real (Y ⁻¹' T))| := by ring_nf
      _ ≤ |ν.real (X ⁻¹' S) - μ.real (X ⁻¹' S)| *
            |ν.real (Y ⁻¹' T)| +
          |μ.real (X ⁻¹' S)| *
            |ν.real (Y ⁻¹' T) - μ.real (Y ⁻¹' T)| := by
              simpa only [abs_mul] using abs_add_le
                ((ν.real (X ⁻¹' S) - μ.real (X ⁻¹' S)) * ν.real (Y ⁻¹' T))
                (μ.real (X ⁻¹' S) *
                  (ν.real (Y ⁻¹' T) - μ.real (Y ⁻¹' T)))
      _ ≤ delta.toReal * 1 + 1 * delta.toReal := by
        gcongr
        · simpa only [abs_sub_comm] using hdX
        · simpa only [abs_of_nonneg hνY0] using hνY1
        · simpa only [abs_of_nonneg hμX0] using hμX1
        · simpa only [abs_sub_comm] using hdY
      _ = 2 * delta.toReal := by ring
  have hgood := hindep S T hS hT
  have htri (a b c : Real) : |a + b + c| ≤ |a| + |b| + |c| := by
    calc
      |a + b + c| ≤ |a + b| + |c| := abs_add_le _ _
      _ ≤ (|a| + |b|) + |c| := add_le_add_left (abs_add_le _ _) _
  calc
    |μ.real (X ⁻¹' S ∩ Y ⁻¹' T) -
        μ.real (X ⁻¹' S) * μ.real (Y ⁻¹' T)| =
      |(μ.real (X ⁻¹' S ∩ Y ⁻¹' T) -
          ν.real (X ⁻¹' S ∩ Y ⁻¹' T)) +
        (ν.real (X ⁻¹' S ∩ Y ⁻¹' T) -
          ν.real (X ⁻¹' S) * ν.real (Y ⁻¹' T)) +
        (ν.real (X ⁻¹' S) * ν.real (Y ⁻¹' T) -
          μ.real (X ⁻¹' S) * μ.real (Y ⁻¹' T))| := by ring_nf
    _ ≤ |μ.real (X ⁻¹' S ∩ Y ⁻¹' T) -
          ν.real (X ⁻¹' S ∩ Y ⁻¹' T)| +
        |ν.real (X ⁻¹' S ∩ Y ⁻¹' T) -
          ν.real (X ⁻¹' S) * ν.real (Y ⁻¹' T)| +
        |ν.real (X ⁻¹' S) * ν.real (Y ⁻¹' T) -
          μ.real (X ⁻¹' S) * μ.real (Y ⁻¹' T)| := htri _ _ _
    _ ≤ delta.toReal + eps + 2 * delta.toReal := by linarith
    _ = eps + 3 * delta.toReal := by ring

/-- A high-probability good part transfers its conditional `NuIndep` theorem to
the full execution.  The `delta ≤ 1/2` assumption both makes conditioning
nondegenerate and is the regime used by the continuing-retry cutoff.

The failure event is `Gᶜ`; the theorem charges it only through the sharp TV
distance between a law and its conditioning on `G`. -/
theorem nuIndep_of_exceptional_condOn
    {Ω A B : Type*} [MeasurableSpace Ω] [MeasurableSpace A] [MeasurableSpace B]
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {X : Ω → A} {Y : Ω → B} (hX : Measurable X) (hY : Measurable Y)
    {G : Set Ω} (hG : MeasurableSet G) {eps : Real} {delta : ENNReal}
    (hdelta : delta ≠ ⊤) (hdeltaHalf : delta ≤ 1 / 2)
    (hfail : μ Gᶜ ≤ delta)
    (hgood : NuIndep (condOn μ G) X Y eps) :
    NuIndep μ X Y (eps + 3 * delta.toReal) := by
  have hbadHalf : μ Gᶜ ≤ 1 / 2 := hfail.trans hdeltaHalf
  have hrestrict : restrictOff μ Gᶜ = condOn μ G := by
    simp only [restrictOff, condOn, compl_compl]
  have hprobRestrict : IsProbabilityMeasure (restrictOff μ Gᶜ) :=
    isProbabilityMeasure_restrictOff hG.compl hbadHalf
  letI : IsProbabilityMeasure (condOn μ G) := hrestrict ▸ hprobRestrict
  have htv : TVLe μ (restrictOff μ Gᶜ) delta :=
    (tvLe_restrictOff hG.compl hbadHalf).mono hfail
  rw [hrestrict] at htv
  exact nuIndep_of_tvLe_measure hX hY hdelta htv hgood

/-! The large-event conditioned-sampler hypothesis can be discharged entirely
inside the good law, then transferred by the preceding theorem. -/

theorem nuIndep_of_exceptional_largeEvent_conditionedSampler
    {Ω A B : Type*} [MeasurableSpace Ω] [MeasurableSpace A] [MeasurableSpace B]
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {τ : Measure B} [IsProbabilityMeasure τ]
    {H : Ω → A} {Y : Ω → B} (hH : Measurable H) (hY : Measurable Y)
    {G : Set Ω} (hG : MeasurableSet G) {delta mix : ENNReal}
    (hdelta : delta ≠ ⊤) (hdeltaHalf : delta ≤ 1 / 2)
    (hfail : μ Gᶜ ≤ delta) (hmixTop : mix ≠ ⊤)
    (nextGiven : Set A → Measure B)
    (hprob : ∀ S : Set A, MeasurableSet S →
      1 / 2 ≤ (condOn μ G).real (H ⁻¹' S) →
      IsProbabilityMeasure (nextGiven S))
    (hfactor : ∀ S : Set A, ∀ T : Set B,
      MeasurableSet S → MeasurableSet T →
      1 / 2 ≤ (condOn μ G).real (H ⁻¹' S) →
      (condOn μ G).real (H ⁻¹' S ∩ Y ⁻¹' T) =
        (condOn μ G).real (H ⁻¹' S) * (nextGiven S).real T)
    (hmix : ∀ S : Set A, MeasurableSet S →
      1 / 2 ≤ (condOn μ G).real (H ⁻¹' S) →
      TVLe (nextGiven S) τ mix) :
    NuIndep μ H Y (2 * mix.toReal + 3 * delta.toReal) := by
  have hbadHalf : μ Gᶜ ≤ 1 / 2 := hfail.trans hdeltaHalf
  have hG0 : μ G ≠ 0 := by
    have hhalf := half_le_measure_compl (sigma := μ) hG.compl hbadHalf
    simpa only [compl_compl] using ne_of_gt ((by norm_num : (0 : ENNReal) < 1 / 2).trans_le hhalf)
  letI : IsProbabilityMeasure (condOn μ G) :=
    isProbabilityMeasure_condOn μ hG0 (measure_ne_top μ G)
  have hgood : NuIndep (condOn μ G) H Y (2 * mix.toReal) :=
    Ttc.CVSequentialDependence.nuIndep_of_largeEvent_conditionedSampler
      hH hY nextGiven hmixTop hprob hfactor hmix
  exact nuIndep_of_exceptional_condOn hH hY hG hdelta hdeltaHalf hfail hgood

#print axioms nuIndep_of_tvLe_measure
#print axioms nuIndep_of_exceptional_condOn
#print axioms nuIndep_of_exceptional_largeEvent_conditionedSampler

end Ttc.CVExceptionalDependence

import Kr25Ssmxt.Analysis.ManuscriptOriginTapeKernelMeasurable

/-! Integrate the Poisson pending-copy count into the measurable ghost tape
transition, with the coin arrays still fixed. -/

namespace Kr25Ssmxt

open MeasureTheory

noncomputable def manuscriptOriginCountTapeLaw
    {n : Nat} (hn : 21 ≤ n) (P : PolytopeData n)
    (b : Nat) (eta threshold : Real)
    (hroute : 1 ≤ decimalScale b * P.inradius ∧
      0 < eta ∧ eta ≤ 1 ∧
      (codedLatticePoints P b).Finite ∧
      (codedLatticePoints P b).Nonempty)
    (intensity : NNReal) (preCoins future : Nat × Nat → Bool)
    (c : ManuscriptOriginConfiguration n) :
    Measure (ManuscriptOriginConfiguration n) :=
  (ProbabilityTheory.poissonMeasure intensity).bind fun basePending =>
    c.tapeAdvanceLaw hn P b eta threshold hroute intensity
      basePending preCoins future

theorem measurable_manuscriptOriginCountTapeLaw
    {n : Nat} (hn : 21 ≤ n) (P : PolytopeData n)
    (b : Nat) (eta threshold : Real) (hthreshold : 0 < threshold)
    (hroute : 1 ≤ decimalScale b * P.inradius ∧
      0 < eta ∧ eta ≤ 1 ∧
      (codedLatticePoints P b).Finite ∧
      (codedLatticePoints P b).Nonempty)
    (intensity : NNReal) (preCoins future : Nat × Nat → Bool) :
    Measurable (manuscriptOriginCountTapeLaw hn P b eta threshold
      hroute intensity preCoins future) := by
  let countLaw := ProbabilityTheory.poissonMeasure intensity
  have hnext : Measurable (fun z : ManuscriptOriginConfiguration n × Nat =>
      z.1.tapeAdvanceLaw hn P b eta threshold hroute intensity
        z.2 preCoins future) := by
    apply measurable_from_prod_countable_left
    intro basePending
    exact measurable_manuscriptOriginTapeAdvanceLaw hn P b eta
      threshold hthreshold hroute intensity basePending preCoins future
  have hbind := measurable_parametric_probability_bind
    (fun _ : ManuscriptOriginConfiguration n => countLaw)
    measurable_const (fun _ => inferInstance)
    (fun z : ManuscriptOriginConfiguration n × Nat =>
      z.1.tapeAdvanceLaw hn P b eta threshold hroute intensity
        z.2 preCoins future) hnext
  exact hbind

theorem manuscriptOriginCountTapeLaw_isProbabilityMeasure
    {n : Nat} (hn : 21 ≤ n) (P : PolytopeData n)
    (b : Nat) (eta threshold : Real)
    (hroute : 1 ≤ decimalScale b * P.inradius ∧
      0 < eta ∧ eta ≤ 1 ∧
      (codedLatticePoints P b).Finite ∧
      (codedLatticePoints P b).Nonempty)
    (intensity : NNReal) (preCoins future : Nat × Nat → Bool)
    (c : ManuscriptOriginConfiguration n) :
    IsProbabilityMeasure (manuscriptOriginCountTapeLaw hn P b eta
      threshold hroute intensity preCoins future c) := by
  unfold manuscriptOriginCountTapeLaw
  exact isProbabilityMeasure_bind
    (measurable_of_countable
      (fun basePending : Nat =>
        c.tapeAdvanceLaw hn P b eta threshold hroute intensity
          basePending preCoins future)).aemeasurable
    (Filter.Eventually.of_forall (fun basePending =>
      c.tapeAdvanceLaw_isProbabilityMeasure hn P b eta threshold hroute
        intensity basePending preCoins future))

noncomputable def manuscriptOriginCountTapeKernel
    {n : Nat} (hn : 21 ≤ n) (P : PolytopeData n)
    (b : Nat) (eta threshold : Real) (hthreshold : 0 < threshold)
    (hroute : 1 ≤ decimalScale b * P.inradius ∧
      0 < eta ∧ eta ≤ 1 ∧
      (codedLatticePoints P b).Finite ∧
      (codedLatticePoints P b).Nonempty)
    (intensity : NNReal) (preCoins future : Nat × Nat → Bool) :
    ProbabilityTheory.Kernel (ManuscriptOriginConfiguration n)
      (ManuscriptOriginConfiguration n) :=
  ⟨manuscriptOriginCountTapeLaw hn P b eta threshold hroute intensity
      preCoins future,
    measurable_manuscriptOriginCountTapeLaw hn P b eta threshold
      hthreshold hroute intensity preCoins future⟩

instance manuscriptOriginCountTapeKernel_isMarkov
    {n : Nat} (hn : 21 ≤ n) (P : PolytopeData n)
    (b : Nat) (eta threshold : Real) (hthreshold : 0 < threshold)
    (hroute : 1 ≤ decimalScale b * P.inradius ∧
      0 < eta ∧ eta ≤ 1 ∧
      (codedLatticePoints P b).Finite ∧
      (codedLatticePoints P b).Nonempty)
    (intensity : NNReal) (preCoins future : Nat × Nat → Bool) :
    ProbabilityTheory.IsMarkovKernel
      (manuscriptOriginCountTapeKernel hn P b eta threshold
        hthreshold hroute intensity preCoins future) :=
  ⟨fun c => manuscriptOriginCountTapeLaw_isProbabilityMeasure hn P b eta
    threshold hroute intensity preCoins future c⟩

end Kr25Ssmxt

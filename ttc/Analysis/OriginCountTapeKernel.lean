import ttc.Analysis.OriginTapeKernelMeasurable

/-! Integrate the Poisson pending-copy count into the measurable ghost tape
transition, with the coin arrays still fixed. -/

namespace ttc

open MeasureTheory

noncomputable def originCountTapeLaw
    {n : Nat} (hn : 21 ≤ n) (P : PolytopeData n)
    (b : Nat) (eta threshold : Real)
    (hroute : samplerRadiusRequirement P eta ≤ decimalScale b * P.inradius ∧
      0 < eta ∧ eta ≤ 1 ∧
      (codedLatticePoints P b).Finite ∧
      (codedLatticePoints P b).Nonempty)
    (intensity : NNReal) (preCoins future : Nat × Nat → Bool)
    (c : OriginConfiguration n) :
    Measure (OriginConfiguration n) :=
  (ProbabilityTheory.poissonMeasure intensity).bind fun basePending =>
    c.tapeAdvanceLaw hn P b eta threshold hroute intensity
      basePending preCoins future

theorem measurable_originCountTapeLaw
    {n : Nat} (hn : 21 ≤ n) (P : PolytopeData n)
    (b : Nat) (eta threshold : Real) (hthreshold : 0 < threshold)
    (hroute : samplerRadiusRequirement P eta ≤ decimalScale b * P.inradius ∧
      0 < eta ∧ eta ≤ 1 ∧
      (codedLatticePoints P b).Finite ∧
      (codedLatticePoints P b).Nonempty)
    (intensity : NNReal) (preCoins future : Nat × Nat → Bool) :
    Measurable (originCountTapeLaw hn P b eta threshold
      hroute intensity preCoins future) := by
  let countLaw := ProbabilityTheory.poissonMeasure intensity
  have hnext : Measurable (fun z : OriginConfiguration n × Nat =>
      z.1.tapeAdvanceLaw hn P b eta threshold hroute intensity
        z.2 preCoins future) := by
    apply measurable_from_prod_countable_left
    intro basePending
    exact measurable_originTapeAdvanceLaw hn P b eta
      threshold hthreshold hroute intensity basePending preCoins future
  have hbind := measurable_parametric_probability_bind
    (fun _ : OriginConfiguration n => countLaw)
    measurable_const (fun _ => inferInstance)
    (fun z : OriginConfiguration n × Nat =>
      z.1.tapeAdvanceLaw hn P b eta threshold hroute intensity
        z.2 preCoins future) hnext
  exact hbind

theorem originCountTapeLaw_isProbabilityMeasure
    {n : Nat} (hn : 21 ≤ n) (P : PolytopeData n)
    (b : Nat) (eta threshold : Real)
    (hroute : samplerRadiusRequirement P eta ≤ decimalScale b * P.inradius ∧
      0 < eta ∧ eta ≤ 1 ∧
      (codedLatticePoints P b).Finite ∧
      (codedLatticePoints P b).Nonempty)
    (intensity : NNReal) (preCoins future : Nat × Nat → Bool)
    (c : OriginConfiguration n) :
    IsProbabilityMeasure (originCountTapeLaw hn P b eta
      threshold hroute intensity preCoins future c) := by
  unfold originCountTapeLaw
  exact isProbabilityMeasure_bind
    (measurable_of_countable
      (fun basePending : Nat =>
        c.tapeAdvanceLaw hn P b eta threshold hroute intensity
          basePending preCoins future)).aemeasurable
    (Filter.Eventually.of_forall (fun basePending =>
      c.tapeAdvanceLaw_isProbabilityMeasure hn P b eta threshold hroute
        intensity basePending preCoins future))

noncomputable def originCountTapeKernel
    {n : Nat} (hn : 21 ≤ n) (P : PolytopeData n)
    (b : Nat) (eta threshold : Real) (hthreshold : 0 < threshold)
    (hroute : samplerRadiusRequirement P eta ≤ decimalScale b * P.inradius ∧
      0 < eta ∧ eta ≤ 1 ∧
      (codedLatticePoints P b).Finite ∧
      (codedLatticePoints P b).Nonempty)
    (intensity : NNReal) (preCoins future : Nat × Nat → Bool) :
    ProbabilityTheory.Kernel (OriginConfiguration n)
      (OriginConfiguration n) :=
  ⟨originCountTapeLaw hn P b eta threshold hroute intensity
      preCoins future,
    measurable_originCountTapeLaw hn P b eta threshold
      hthreshold hroute intensity preCoins future⟩

instance originCountTapeKernel_isMarkov
    {n : Nat} (hn : 21 ≤ n) (P : PolytopeData n)
    (b : Nat) (eta threshold : Real) (hthreshold : 0 < threshold)
    (hroute : samplerRadiusRequirement P eta ≤ decimalScale b * P.inradius ∧
      0 < eta ∧ eta ≤ 1 ∧
      (codedLatticePoints P b).Finite ∧
      (codedLatticePoints P b).Nonempty)
    (intensity : NNReal) (preCoins future : Nat × Nat → Bool) :
    ProbabilityTheory.IsMarkovKernel
      (originCountTapeKernel hn P b eta threshold
        hthreshold hroute intensity preCoins future) :=
  ⟨fun c => originCountTapeLaw_isProbabilityMeasure hn P b eta
    threshold hroute intensity preCoins future c⟩

end ttc

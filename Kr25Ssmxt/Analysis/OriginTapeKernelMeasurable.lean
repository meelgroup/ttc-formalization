import Kr25Ssmxt.Analysis.OriginAdvanceStateMeasurable

/-! A measurable ghost transition kernel for the independent normalized
Hit-and-Run point tape after the count and coin choices are fixed. -/

namespace Kr25Ssmxt

open MeasureTheory

theorem measurable_originTapeAdvanceLaw
    {n : Nat} (hn : 21 ≤ n) (P : PolytopeData n)
    (b : Nat) (eta threshold : Real) (hthreshold : 0 < threshold)
    (hroute : samplerRadiusRequirement P eta ≤ decimalScale b * P.inradius ∧
      0 < eta ∧ eta ≤ 1 ∧
      (codedLatticePoints P b).Finite ∧
      (codedLatticePoints P b).Nonempty)
    (intensity : NNReal) (basePending : Nat)
    (preCoins future : Nat × Nat → Bool) :
    Measurable (fun c : OriginConfiguration n =>
      c.tapeAdvanceLaw hn P b eta threshold hroute intensity
        basePending preCoins future) := by
  let pointLaw := normalizedHitAndRunPointLaw hn P b eta hroute.1
    hroute.2.1 hroute.2.2.1 hroute.2.2.2.1 hroute.2.2.2.2
  letI : IsProbabilityMeasure pointLaw :=
    (P.normalizedHitAndRun_latticePointLaw hn b hroute.1
      hroute.2.1 hroute.2.2.1 hroute.2.2.2.1 hroute.2.2.2.2).1
  let sourceLaw : Measure (Nat → LatticePoint n) :=
    Measure.infinitePi (fun _ : Nat => pointLaw)
  letI : ∀ _ : Nat, IsProbabilityMeasure pointLaw := fun _ => inferInstance
  letI : IsProbabilityMeasure sourceLaw := by
    dsimp [sourceLaw]
    infer_instance
  have hnext : Measurable (fun z : OriginConfiguration n ×
      (Nat → LatticePoint n) =>
      Measure.dirac (z.1.advance P intensity threshold basePending
        preCoins future z.2)) :=
    Measure.measurable_dirac.comp
      (OriginConfiguration.measurable_advance_joint P intensity
        threshold hthreshold basePending preCoins future)
  have hbind := measurable_parametric_probability_bind
    (fun _ : OriginConfiguration n => sourceLaw)
    measurable_const (fun _ => inferInstance)
    (fun z : OriginConfiguration n × (Nat → LatticePoint n) =>
      Measure.dirac (z.1.advance P intensity threshold basePending
        preCoins future z.2)) hnext
  convert hbind using 1
  funext c
  exact (Measure.bind_dirac_eq_map sourceLaw
    (c.measurable_advance_tape P intensity threshold basePending
      preCoins future)).symm

noncomputable def originTapeAdvanceKernel
    {n : Nat} (hn : 21 ≤ n) (P : PolytopeData n)
    (b : Nat) (eta threshold : Real) (hthreshold : 0 < threshold)
    (hroute : samplerRadiusRequirement P eta ≤ decimalScale b * P.inradius ∧
      0 < eta ∧ eta ≤ 1 ∧
      (codedLatticePoints P b).Finite ∧
      (codedLatticePoints P b).Nonempty)
    (intensity : NNReal) (basePending : Nat)
    (preCoins future : Nat × Nat → Bool) :
    ProbabilityTheory.Kernel (OriginConfiguration n)
      (OriginConfiguration n) :=
  ⟨fun c => c.tapeAdvanceLaw hn P b eta threshold hroute intensity
      basePending preCoins future,
    measurable_originTapeAdvanceLaw hn P b eta threshold
      hthreshold hroute intensity basePending preCoins future⟩

instance originTapeAdvanceKernel_isMarkov
    {n : Nat} (hn : 21 ≤ n) (P : PolytopeData n)
    (b : Nat) (eta threshold : Real) (hthreshold : 0 < threshold)
    (hroute : samplerRadiusRequirement P eta ≤ decimalScale b * P.inradius ∧
      0 < eta ∧ eta ≤ 1 ∧
      (codedLatticePoints P b).Finite ∧
      (codedLatticePoints P b).Nonempty)
    (intensity : NNReal) (basePending : Nat)
    (preCoins future : Nat × Nat → Bool) :
    ProbabilityTheory.IsMarkovKernel
      (originTapeAdvanceKernel hn P b eta threshold
        hthreshold hroute intensity basePending preCoins future) :=
  ⟨fun c => c.tapeAdvanceLaw_isProbabilityMeasure hn P b eta threshold
    hroute intensity basePending preCoins future⟩

end Kr25Ssmxt

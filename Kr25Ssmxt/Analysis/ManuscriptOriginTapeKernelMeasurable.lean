import Kr25Ssmxt.Analysis.ManuscriptOriginAdvanceStateMeasurable

/-! A measurable ghost transition kernel for the independent normalized
Hit-and-Run point tape after the count and coin choices are fixed. -/

namespace Kr25Ssmxt

open MeasureTheory

theorem measurable_manuscriptOriginTapeAdvanceLaw
    {n : Nat} (hn : 21 ≤ n) (P : PolytopeData n)
    (b : Nat) (eta threshold : Real) (hthreshold : 0 < threshold)
    (hroute : 1 ≤ decimalScale b * P.inradius ∧
      0 < eta ∧ eta ≤ 1 ∧
      (codedLatticePoints P b).Finite ∧
      (codedLatticePoints P b).Nonempty)
    (intensity : NNReal) (basePending : Nat)
    (preCoins future : Nat × Nat → Bool) :
    Measurable (fun c : ManuscriptOriginConfiguration n =>
      c.tapeAdvanceLaw hn P b eta threshold hroute intensity
        basePending preCoins future) := by
  let pointLaw := normalizedHitAndRunPointLaw hn P b hroute.1 eta
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
  have hnext : Measurable (fun z : ManuscriptOriginConfiguration n ×
      (Nat → LatticePoint n) =>
      Measure.dirac (z.1.advance P intensity threshold basePending
        preCoins future z.2)) :=
    Measure.measurable_dirac.comp
      (ManuscriptOriginConfiguration.measurable_advance_joint P intensity
        threshold hthreshold basePending preCoins future)
  have hbind := measurable_parametric_probability_bind
    (fun _ : ManuscriptOriginConfiguration n => sourceLaw)
    measurable_const (fun _ => inferInstance)
    (fun z : ManuscriptOriginConfiguration n × (Nat → LatticePoint n) =>
      Measure.dirac (z.1.advance P intensity threshold basePending
        preCoins future z.2)) hnext
  convert hbind using 1
  funext c
  exact (Measure.bind_dirac_eq_map sourceLaw
    (c.measurable_advance_tape P intensity threshold basePending
      preCoins future)).symm

noncomputable def manuscriptOriginTapeAdvanceKernel
    {n : Nat} (hn : 21 ≤ n) (P : PolytopeData n)
    (b : Nat) (eta threshold : Real) (hthreshold : 0 < threshold)
    (hroute : 1 ≤ decimalScale b * P.inradius ∧
      0 < eta ∧ eta ≤ 1 ∧
      (codedLatticePoints P b).Finite ∧
      (codedLatticePoints P b).Nonempty)
    (intensity : NNReal) (basePending : Nat)
    (preCoins future : Nat × Nat → Bool) :
    ProbabilityTheory.Kernel (ManuscriptOriginConfiguration n)
      (ManuscriptOriginConfiguration n) :=
  ⟨fun c => c.tapeAdvanceLaw hn P b eta threshold hroute intensity
      basePending preCoins future,
    measurable_manuscriptOriginTapeAdvanceLaw hn P b eta threshold
      hthreshold hroute intensity basePending preCoins future⟩

instance manuscriptOriginTapeAdvanceKernel_isMarkov
    {n : Nat} (hn : 21 ≤ n) (P : PolytopeData n)
    (b : Nat) (eta threshold : Real) (hthreshold : 0 < threshold)
    (hroute : 1 ≤ decimalScale b * P.inradius ∧
      0 < eta ∧ eta ≤ 1 ∧
      (codedLatticePoints P b).Finite ∧
      (codedLatticePoints P b).Nonempty)
    (intensity : NNReal) (basePending : Nat)
    (preCoins future : Nat × Nat → Bool) :
    ProbabilityTheory.IsMarkovKernel
      (manuscriptOriginTapeAdvanceKernel hn P b eta threshold
        hthreshold hroute intensity basePending preCoins future) :=
  ⟨fun c => c.tapeAdvanceLaw_isProbabilityMeasure hn P b eta threshold
    hroute intensity basePending preCoins future⟩

end Kr25Ssmxt

import Kr25Ssmxt.Analysis.ManuscriptDyadicCutoff
import Kr25Ssmxt.Analysis.ManuscriptPointIntensity
import Kr25Ssmxt.Analysis.TtcVolumeAccuracyLatticeComparison

/-! The first manuscript while-loop cannot cross the final lattice cutoff
after a successful component volume estimate. -/

namespace Kr25Ssmxt

open MeasureTheory

theorem manuscript_no_first_halving_at_cutoff
    {n k : Nat} (hn : 0 < n) {F : LRAFormula n k}
    (D : Decomposition F) (p : ApproxParams) (b : Nat)
    (hprecision : PrecisionAdequate D b p.precisionEta)
    (hcomponents : 0 < D.componentCount)
    (i : Fin D.componentCount)
    (volumeEstimate : NNReal)
    (hvolume : (volumeEstimate : Real) ∈
      Arlib.relErr p.ε'
        (volume (D.component i).carrier).toReal)
    (s : TTCState n)
    (hrate : (s.p : Real) =
      1 / (2 : Real) ^
        (manuscriptDyadicCutoff (D.latticePoints b).ncard - 1)) :
    manuscriptRateExit s
      (ttc.t b n (p.Thresh D.componentCount) volumeEstimate)
      (p.Thresh D.componentCount) = 0 := by
  let count := (D.latticePoints b).ncard
  have hcount : 0 < count :=
    manuscript_union_lattice_ncard_pos hn D p b hprecision hcomponents
  have hcomponentCount :
      ((D.component i).carrier ∩ decimalLattice b n).ncard ≤ count :=
    manuscript_component_lattice_ncard_le_union hn D p b hprecision i
  have hlattice := (ttc_volume_accuracy_lattice_comparison hn D p b hprecision).1 i
  have hintensity := manuscriptIntensity_le_four_thirds n b p
    (p.Thresh D.componentCount) (p.threshold_pos D.componentCount).le
    volumeEstimate (volume (D.component i).carrier).toReal
    ((D.component i).carrier ∩ decimalLattice b n).ncard count
    hcomponentCount hvolume hlattice
  exact manuscriptRateExit_zero_at_cutoff s
    (ttc.t b n (p.Thresh D.componentCount) volumeEstimate)
    count hcount (p.Thresh D.componentCount)
    (p.threshold_pos D.componentCount) hrate hintensity

/-- The same bound applies to a first while-loop entered at any dyadic level
before the cutoff: it cannot jump past the cutoff in one component. -/
theorem manuscript_no_first_halving_past_cutoff
    {n k : Nat} (hn : 0 < n) {F : LRAFormula n k}
    (D : Decomposition F) (p : ApproxParams) (b : Nat)
    (hprecision : PrecisionAdequate D b p.precisionEta)
    (hcomponents : 0 < D.componentCount)
    (i : Fin D.componentCount)
    (volumeEstimate : NNReal)
    (hvolume : (volumeEstimate : Real) ∈
      Arlib.relErr p.ε'
        (volume (D.component i).carrier).toReal)
    (s : TTCState n) (level : Nat)
    (hlevel : level ≤ manuscriptDyadicCutoff (D.latticePoints b).ncard - 1)
    (hrate : s.p = 1 / (2 : NNReal) ^ level) :
    manuscriptRateExit s
      (ttc.t b n (p.Thresh D.componentCount) volumeEstimate)
      (p.Thresh D.componentCount) ≤
        manuscriptDyadicCutoff (D.latticePoints b).ncard - 1 - level := by
  let count := (D.latticePoints b).ncard
  have hcount : 0 < count :=
    manuscript_union_lattice_ncard_pos hn D p b hprecision hcomponents
  have hcomponentCount :
      ((D.component i).carrier ∩ decimalLattice b n).ncard ≤ count :=
    manuscript_component_lattice_ncard_le_union hn D p b hprecision i
  have hlattice :=
    (ttc_volume_accuracy_lattice_comparison hn D p b hprecision).1 i
  have hintensity := manuscriptIntensity_le_four_thirds n b p
    (p.Thresh D.componentCount) (p.threshold_pos D.componentCount).le
    volumeEstimate (volume (D.component i).carrier).toReal
    ((D.component i).carrier ∩ decimalLattice b n).ncard count
    hcomponentCount hvolume hlattice
  exact manuscriptRateExit_le_cutoff_gap s
    (ttc.t b n (p.Thresh D.componentCount) volumeEstimate)
    count hcount (p.Thresh D.componentCount)
    (p.threshold_pos D.componentCount) level hlevel hrate hintensity

/-- If the count-thinning loop jumps across the cutoff, its fixed-level
population at the cutoff already violates the loop's threshold. -/
theorem manuscript_second_loop_jump_past_cutoff_large_population
    {n : Nat} (s : TTCState n) (pending : Nat)
    (threshold : Real) (coins : Nat × Nat → Bool)
    (count level : Nat)
    (hlevel : level ≤ manuscriptDyadicCutoff count - 1)
    (hjump : manuscriptDyadicCutoff count - 1 <
      level + firstExitRound s pending threshold coins) :
    threshold <
      (samplesAfter coins
        (manuscriptDyadicCutoff count - 1 - level) s.X).card +
      pendingAfter coins
        (manuscriptDyadicCutoff count - 1 - level)
        s.nextLabel pending := by
  apply manuscript_second_loop_crossing_implies_large_population
  omega

end Kr25Ssmxt

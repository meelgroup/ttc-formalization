import Kr25Ssmxt.Analysis.OracleContracts
import Kr25Ssmxt.Analysis.StateMarking
import Kr25Ssmxt.Analysis.ConcreteComponentStep
import Kr25Ssmxt.Analysis.BernoulliCount

/-! Poisson marking for the actual paper sampler applied to a labelled
TTC state, on its certified normalized branch. -/

namespace Kr25Ssmxt

open Classical MeasureTheory ProbabilityTheory

theorem community_poisson_append_pointCounts_law
    {n k : Nat} (hn : 21 ≤ n) (prep : TTCPreprocessor n k)
    (s : TTCState n) (hs : s.LabelsFresh)
    (P : PolytopeData n) (b : Nat) (eta delta : Real)
    (hroute : samplerRadiusRequirement P eta ≤ decimalScale b * P.inradius ∧
      0 < eta ∧ eta ≤ 1 ∧
      (codedLatticePoints P b).Finite ∧
      (codedLatticePoints P b).Nonempty)
    (S : Finset (LatticePoint n))
    (hsubset : codedLatticePoints P b ⊆ (S : Set (LatticePoint n)))
    (mean : NNReal) :
    let pointLaw := normalizedHitAndRunPointLaw hn P b eta hroute.1
      hroute.2.1 hroute.2.2.1 hroute.2.2.2.1 hroute.2.2.2.2
    ((poissonMeasure mean).bind fun count =>
      ((ttcSubroutines hn prep).GenerateSamples
        P count b eta).map
        (fun batch => (s.addBatch batch).pointCounts S)) =
      (Measure.pi (fun x : S => poissonMeasure (Real.toNNReal
        (pointLaw.real {(x : LatticePoint n)} * (mean : Real))))).map
        (fun fresh x => s.pointCounts S x + fresh x) := by
  dsimp only
  let pointLaw := normalizedHitAndRunPointLaw hn P b eta hroute.1
    hroute.2.1 hroute.2.2.1 hroute.2.2.2.1 hroute.2.2.2.2
  have halmost : AlmostUniformPointwise pointLaw (codedLatticePoints P b) eta :=
    P.normalizedHitAndRun_latticePointLaw hn b hroute.1
      hroute.2.1 hroute.2.2.1 hroute.2.2.2.1 hroute.2.2.2.2
  letI : IsProbabilityMeasure pointLaw := halmost.1
  have hsupport : pointLaw (S : Set (LatticePoint n))ᶜ = 0 := by
    have hsmall : (S : Set (LatticePoint n))ᶜ ⊆
        (codedLatticePoints P b)ᶜ := Set.compl_subset_compl.mpr hsubset
    exact nonpos_iff_eq_zero.mp ((measure_mono hsmall).trans_eq
      (by simpa using halmost.2.2.2.1))
  simp_rw [community_generateSamples_eq_iid hn prep P _ b eta delta hroute]
  exact poisson_append_pointCounts_law s hs pointLaw S hsupport mean

/-- Actual overlap deletion followed by the concrete sampler has the
delete-and-add Poisson point-count law used by the fixed-level analysis. -/
theorem community_poisson_delete_append_pointCounts_law
    {n k : Nat} (hn : 21 ≤ n) (prep : TTCPreprocessor n k)
    (s : TTCState n) (hs : s.LabelsFresh)
    (P : PolytopeData n) (b : Nat) (eta delta : Real)
    (hroute : samplerRadiusRequirement P eta ≤ decimalScale b * P.inradius ∧
      0 < eta ∧ eta ≤ 1 ∧
      (codedLatticePoints P b).Finite ∧
      (codedLatticePoints P b).Nonempty)
    (S : Finset (LatticePoint n))
    (hsubset : codedLatticePoints P b ⊆ (S : Set (LatticePoint n)))
    (mean : NNReal) :
    let pointLaw := normalizedHitAndRunPointLaw hn P b eta hroute.1
      hroute.2.1 hroute.2.2.1 hroute.2.2.2.1 hroute.2.2.2.2
    ((poissonMeasure mean).bind fun count =>
      ((ttcSubroutines hn prep).GenerateSamples
        P count b eta).map
        (fun batch => ((s.removeComponent P).addBatch batch).pointCounts S)) =
      (Measure.pi (fun x : S => poissonMeasure (Real.toNNReal
        (pointLaw.real {(x : LatticePoint n)} * (mean : Real))))).map
        (fun fresh x =>
          (if x.1.toPoint ∈ P.carrier then 0 else s.pointCounts S x) + fresh x) := by
  rw [community_poisson_append_pointCounts_law hn prep
    (s.removeComponent P) (s.labelsFresh_removeComponent P hs)
    P b eta delta hroute S hsubset mean]
  congr 1
  funext fresh x
  rw [s.pointCounts_removeComponent P S]

/-- A fixed number of actual second-loop thinning rounds followed by the
concrete sampler has the expected Poisson vector law on the labelled state. -/
theorem community_fixed_round_append_pointCounts_law
    {n k : Nat} (hn : 21 ≤ n) (prep : TTCPreprocessor n k)
    (s : TTCState n) (hs : s.LabelsFresh)
    (P : PolytopeData n) (b : Nat) (eta delta : Real)
    (hroute : samplerRadiusRequirement P eta ≤ decimalScale b * P.inradius ∧
      0 < eta ∧ eta ≤ 1 ∧
      (codedLatticePoints P b).Finite ∧
      (codedLatticePoints P b).Nonempty)
    (S : Finset (LatticePoint n))
    (hsubset : codedLatticePoints P b ⊆ (S : Set (LatticePoint n)))
    (mean : NNReal) (firstLabel rounds : Nat) :
    let pointLaw := normalizedHitAndRunPointLaw hn P b eta hroute.1
      hroute.2.1 hroute.2.2.1 hroute.2.2.2.1 hroute.2.2.2.2
    ((poissonMeasure mean).bind fun pending =>
      (fairCoinStreamLaw.map (fun coins =>
        pendingAfter coins rounds firstLabel pending)).bind fun count =>
        ((ttcSubroutines hn prep).GenerateSamples
          P count b eta).map
          (fun batch => (s.addBatch batch).pointCounts S)) =
      (Measure.pi (fun x : S => poissonMeasure (Real.toNNReal
        (pointLaw.real {(x : LatticePoint n)} *
          ((unitInterval.toNNReal (survivalProbability rounds) * mean : NNReal) : Real))))).map
        (fun fresh x => s.pointCounts S x + fresh x) := by
  dsimp only
  let K : Nat → Measure Nat := fun pending =>
    fairCoinStreamLaw.map (fun coins =>
      pendingAfter coins rounds firstLabel pending)
  let G : Nat → Measure (S → Nat) := fun count =>
    ((ttcSubroutines hn prep).GenerateSamples
      P count b eta).map
      (fun batch => (s.addBatch batch).pointCounts S)
  change (poissonMeasure mean).bind (fun pending => (K pending).bind G) = _
  calc
    (poissonMeasure mean).bind (fun pending => (K pending).bind G) =
      ((poissonMeasure mean).bind K).bind G := by
        exact (Measure.bind_bind Measurable.of_discrete.aemeasurable
          Measurable.of_discrete.aemeasurable).symm
    _ = (poissonMeasure
        (unitInterval.toNNReal (survivalProbability rounds) * mean)).bind G := by
          rw [show (poissonMeasure mean).bind K =
            poissonMeasure
              (unitInterval.toNNReal (survivalProbability rounds) * mean) from
              poisson_pendingAfter_law mean firstLabel rounds]
    _ = _ := community_poisson_append_pointCounts_law hn prep
      s hs P b eta delta hroute S hsubset
      (unitInterval.toNNReal (survivalProbability rounds) * mean)

/-- The fixed-round law also includes the paper's overlap deletion. -/
theorem community_fixed_round_delete_append_pointCounts_law
    {n k : Nat} (hn : 21 ≤ n) (prep : TTCPreprocessor n k)
    (s : TTCState n) (hs : s.LabelsFresh)
    (P : PolytopeData n) (b : Nat) (eta delta : Real)
    (hroute : samplerRadiusRequirement P eta ≤ decimalScale b * P.inradius ∧
      0 < eta ∧ eta ≤ 1 ∧
      (codedLatticePoints P b).Finite ∧
      (codedLatticePoints P b).Nonempty)
    (S : Finset (LatticePoint n))
    (hsubset : codedLatticePoints P b ⊆ (S : Set (LatticePoint n)))
    (mean : NNReal) (firstLabel rounds : Nat) :
    let pointLaw := normalizedHitAndRunPointLaw hn P b eta hroute.1
      hroute.2.1 hroute.2.2.1 hroute.2.2.2.1 hroute.2.2.2.2
    ((poissonMeasure mean).bind fun pending =>
      (fairCoinStreamLaw.map (fun coins =>
        pendingAfter coins rounds firstLabel pending)).bind fun count =>
        ((ttcSubroutines hn prep).GenerateSamples
          P count b eta).map
          (fun batch => ((s.removeComponent P).addBatch batch).pointCounts S)) =
      (Measure.pi (fun x : S => poissonMeasure (Real.toNNReal
        (pointLaw.real {(x : LatticePoint n)} *
          ((unitInterval.toNNReal (survivalProbability rounds) * mean : NNReal) : Real))))).map
        (fun fresh x =>
          (if x.1.toPoint ∈ P.carrier then 0 else s.pointCounts S x) + fresh x) := by
  rw [community_fixed_round_append_pointCounts_law hn prep
    (s.removeComponent P) (s.labelsFresh_removeComponent P hs)
    P b eta delta hroute S hsubset mean firstLabel rounds]
  congr 1
  funext fresh x
  rw [s.pointCounts_removeComponent P S]

end Kr25Ssmxt

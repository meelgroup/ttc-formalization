import ttc.Analysis.OracleContracts
import ttc.Analysis.PrecisionRequirements
import ttc.Analysis.FixedLevelIntensity
import ttc.Analysis.PointIntensity
import ttc.Analysis.StateMarking

/-! The fixed-level delete-and-append step with rates drawn from one
paper component's scaled volume estimate and point sampler. -/

namespace ttc

open Classical MeasureTheory

noncomputable def componentFixedLevelStep
    {n : Nat} (S : Finset (LatticePoint n)) (T : Finset S)
    (pointLaw : Measure (LatticePoint n))
    (b : Nat) (threshold : Real) (volumeEstimate rate : NNReal) :
    FixedLevelStep S where
  deleted := T
  incoming := fun x => Real.toNNReal
    (pointLaw.real {(x.1 : LatticePoint n)} *
      ((ttcReference.t b n threshold volumeEstimate * rate : NNReal) : Real))

theorem componentFixedLevelStep_envelope
    {n : Nat} (S : Finset (LatticePoint n)) (T : Finset S)
    (pointLaw : Measure (LatticePoint n))
    (b : Nat) (threshold : Real) (hthreshold : 0 ≤ threshold)
    (volumeEstimate rate : NNReal)
    (componentVolume : Real) (cardinality : Nat)
    (hcardinality : 0 < cardinality)
    (ε' latticeEta : Real)
    (hepsilonPrime : 0 ≤ ε')
    (hepsilonPrime_le_one : ε' ≤ 1)
    (hlatticeEta : 0 ≤ latticeEta)
    (hlatticeEta_le_one : latticeEta ≤ 1)
    (hvolume : (volumeEstimate : Real) ∈
      Arlib.relErr ε' componentVolume)
    (hlattice : componentVolume ∈ Arlib.relErr latticeEta
      ((cardinality : Real) / (10 : Real) ^ (b * n)))
    (hpoint : ∀ x ∈ T,
      pointLaw.real {(x.1 : LatticePoint n)} ∈
        Arlib.relErr ε' (1 / (cardinality : Real)))
    (hzero : ∀ x : S, x ∉ T →
      pointLaw.real {(x.1 : LatticePoint n)} = 0) :
    (componentFixedLevelStep S T pointLaw b threshold
      volumeEstimate rate).RateEnvelope
        (Real.toNNReal (threshold * (1 - ε') ^ 2 *
          (1 - latticeEta) * rate))
        (Real.toNNReal (threshold * (1 + ε') ^ 2 *
          (1 + latticeEta) * rate)) := by
  constructor
  · intro x hx
    have hbounds := point_intensity_bounds n b threshold hthreshold
      volumeEstimate componentVolume (pointLaw.real {(x.1 : LatticePoint n)})
      rate cardinality hcardinality ε' latticeEta
      hepsilonPrime hepsilonPrime_le_one hlatticeEta hlatticeEta_le_one
      hvolume hlattice (hpoint x hx)
    constructor
    · apply Real.toNNReal_mono
      calc
        threshold * (1 - ε') ^ 2 * (1 - latticeEta) *
            (rate : Real) ≤
          (ttcReference.t b n threshold volumeEstimate : Real) *
            rate * pointLaw.real {(x.1 : LatticePoint n)} := hbounds.1
        _ = pointLaw.real {(x.1 : LatticePoint n)} *
              ((ttcReference.t b n threshold volumeEstimate * rate : NNReal) : Real) := by
          rw [NNReal.coe_mul]
          ring
    · apply Real.toNNReal_mono
      calc
        pointLaw.real {(x.1 : LatticePoint n)} *
            ((ttcReference.t b n threshold volumeEstimate * rate : NNReal) : Real) =
          (ttcReference.t b n threshold volumeEstimate : Real) *
            rate * pointLaw.real {(x.1 : LatticePoint n)} := by
          rw [NNReal.coe_mul]
          ring
        _ ≤ threshold * (1 + ε') ^ 2 *
            (1 + latticeEta) * (rate : Real) := hbounds.2
  · intro x hx
    simp [componentFixedLevelStep, hzero x hx]

theorem AlmostUniformPointwise.pointMass_zero_of_not_mem
    {n : Nat} {pointLaw : Measure (LatticePoint n)}
    {U : Set (LatticePoint n)} {eta : Real}
    (h : AlmostUniformPointwise pointLaw U eta)
    (x : LatticePoint n) (hx : x ∉ U) :
    pointLaw.real {x} = 0 := by
  have hsub : ({x} : Set (LatticePoint n)) ⊆ Uᶜ := by
    intro y hy
    simpa only [Set.mem_singleton_iff] using hy ▸ hx
  have hmeasure : pointLaw {x} = 0 :=
    le_antisymm ((measure_mono hsub).trans_eq h.2.2.2.1) bot_le
  simp [Measure.real, hmeasure]

/-- The concrete almost-uniform point-law contract supplies every pointwise
rate and support condition required by a fixed-level component step. -/
theorem componentFixedLevelStep_envelope_of_almostUniform
    {n : Nat} (S : Finset (LatticePoint n)) (T : Finset S)
    (pointLaw : Measure (LatticePoint n))
    (U : Set (LatticePoint n))
    (b : Nat) (threshold : Real) (hthreshold : 0 ≤ threshold)
    (volumeEstimate rate : NNReal)
    (componentVolume : Real)
    (ε' latticeEta : Real)
    (hepsilonPrime : 0 ≤ ε')
    (hepsilonPrime_le_one : ε' ≤ 1)
    (hlatticeEta : 0 ≤ latticeEta)
    (hlatticeEta_le_one : latticeEta ≤ 1)
    (hvolume : (volumeEstimate : Real) ∈
      Arlib.relErr ε' componentVolume)
    (hlattice : componentVolume ∈ Arlib.relErr latticeEta
      ((U.ncard : Real) / (10 : Real) ^ (b * n)))
    (halmost : AlmostUniformPointwise pointLaw U ε')
    (hT : ∀ x : S, x ∈ T ↔ x.1 ∈ U) :
    (componentFixedLevelStep S T pointLaw b threshold
      volumeEstimate rate).RateEnvelope
        (Real.toNNReal (threshold * (1 - ε') ^ 2 *
          (1 - latticeEta) * rate))
        (Real.toNNReal (threshold * (1 + ε') ^ 2 *
          (1 + latticeEta) * rate)) := by
  have hcard : 0 < U.ncard :=
    (Set.ncard_pos halmost.2.1).mpr halmost.2.2.1
  apply componentFixedLevelStep_envelope S T pointLaw b
    threshold hthreshold volumeEstimate rate componentVolume U.ncard hcard
    ε' latticeEta hepsilonPrime hepsilonPrime_le_one
    hlatticeEta hlatticeEta_le_one hvolume hlattice
  · intro x hx
    exact halmost.2.2.2.2 x.1 ((hT x).mp hx)
  · intro x hx
    exact halmost.pointMass_zero_of_not_mem x
      (fun hmem => hx ((hT x).mpr hmem))

end ttc

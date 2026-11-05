import Kr25Ssmxt.Analysis.ProcessComponentsLatticeCountAccuracyParameterEnvelope
import Kr25Ssmxt.Analysis.ManuscriptDyadicRate

/-! Convert the manuscript's fixed-level population envelope into the
intermediate relative-error estimate of the scaled lattice count. -/

namespace Kr25Ssmxt

theorem manuscriptEstimate_of_population_envelope
    {n : Nat} (s : TTCState n) (b count : Nat)
    (p : ApproxParams) (threshold : Real) (hthreshold : 0 < threshold)
    (hrate : 0 < (s.rate : Real))
    (hlower :
      (1 - p.epsilonPrime) ^ 3 * (1 - p.latticeEta) *
        threshold * count * (s.rate : Real) ≤ s.samples.card)
    (hupper :
      (s.samples.card : Real) ≤
        (1 + p.epsilonPrime) ^ 3 * (1 + p.latticeEta) *
          threshold * count * (s.rate : Real)) :
    (manuscriptEstimate b threshold s : Real) ∈
      Arlib.relErr (p.epsilon / 2)
        ((count : Real) / (10 : Real) ^ (b * n)) := by
  let scale : Real := (10 : Real) ^ (b * n)
  have hscale : 0 < scale := by dsimp [scale]; positivity
  have hdenom : 0 < (s.rate : Real) * threshold * scale := by positivity
  have hcount : (0 : Real) ≤ count := Nat.cast_nonneg _
  have hbase := process_components_lattice_count_accuracy_parameter_envelope p
  have hmult : 0 ≤ (count : Real) * threshold * (s.rate : Real) := by positivity
  have htargetLower :
      (1 - p.epsilon / 2) * count * (s.rate : Real) * threshold ≤
        (s.samples.card : Real) := by
    calc
      (1 - p.epsilon / 2) * count * (s.rate : Real) * threshold ≤
          (1 - p.epsilonPrime) ^ 3 * (1 - p.latticeEta) *
            threshold * count * (s.rate : Real) := by
        have h := mul_le_mul_of_nonneg_right hbase.1 hmult
        nlinarith
      _ ≤ (s.samples.card : Real) := hlower
  have htargetUpper :
      (s.samples.card : Real) ≤
        (1 + p.epsilon / 2) * count * (s.rate : Real) * threshold := by
    calc
      (s.samples.card : Real) ≤
          (1 + p.epsilonPrime) ^ 3 * (1 + p.latticeEta) *
            threshold * count * (s.rate : Real) := hupper
      _ ≤ (1 + p.epsilon / 2) * count * (s.rate : Real) * threshold := by
        have h := mul_le_mul_of_nonneg_right hbase.2 hmult
        nlinarith
  have hestimate : (manuscriptEstimate b threshold s : Real) =
      (s.samples.card : Real) / ((s.rate : Real) * threshold * scale) := by
    simp [manuscriptEstimate, scale, Real.coe_toNNReal threshold hthreshold.le]
  rw [Arlib.mem_relErr, hestimate]
  constructor
  · change (1 - p.epsilon / 2) * ((count : Real) / scale) ≤
        (s.samples.card : Real) / ((s.rate : Real) * threshold * scale)
    rw [← mul_div_assoc]
    apply (div_le_div_iff₀ hscale hdenom).2
    calc
      ((1 - p.epsilon / 2) * count) * ((s.rate : Real) * threshold * scale) =
          ((1 - p.epsilon / 2) * count * (s.rate : Real) * threshold) * scale := by ring
      _ ≤ (s.samples.card : Real) * scale :=
        mul_le_mul_of_nonneg_right htargetLower hscale.le
  · change (s.samples.card : Real) / ((s.rate : Real) * threshold * scale) ≤
        (1 + p.epsilon / 2) * ((count : Real) / scale)
    rw [← mul_div_assoc]
    apply (div_le_div_iff₀ hdenom hscale).2
    calc
      (s.samples.card : Real) * scale ≤
          ((1 + p.epsilon / 2) * count * (s.rate : Real) * threshold) * scale :=
        mul_le_mul_of_nonneg_right htargetUpper hscale.le
      _ = ((1 + p.epsilon / 2) * count) *
            ((s.rate : Real) * threshold * scale) := by ring

end Kr25Ssmxt

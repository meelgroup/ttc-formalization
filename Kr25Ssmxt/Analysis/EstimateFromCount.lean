import Kr25Ssmxt.Analysis.PrecisionRequirements
import Kr25Ssmxt.Analysis.ProcessComponentsLatticeCountAccuracyParameterEnvelope
import Kr25Ssmxt.Analysis.DyadicRate

/-! Convert the paper's fixed-level population envelope into the
intermediate relative-error estimate of the scaled lattice count. -/

namespace Kr25Ssmxt

theorem estimate_of_population_envelope
    {n : Nat} (s : TTCState n) (b count : Nat)
    (p : ApproxParams) (threshold : Real) (hthreshold : 0 < threshold)
    (hrate : 0 < (s.p : Real))
    (hlower :
      (1 - p.ε') ^ 3 * (1 - p.latticeEta) *
        threshold * count * (s.p : Real) ≤ s.X.card)
    (hupper :
      (s.X.card : Real) ≤
        (1 + p.ε') ^ 3 * (1 + p.latticeEta) *
          threshold * count * (s.p : Real)) :
    (Est b threshold s : Real) ∈
      Arlib.relErr (p.epsilon / 2)
        ((count : Real) / (10 : Real) ^ (b * n)) := by
  let scale : Real := (10 : Real) ^ (b * n)
  have hscale : 0 < scale := by dsimp [scale]; positivity
  have hdenom : 0 < (s.p : Real) * threshold * scale := by positivity
  have hcount : (0 : Real) ≤ count := Nat.cast_nonneg _
  have hbase := process_components_lattice_count_accuracy_parameter_envelope p
  have hmult : 0 ≤ (count : Real) * threshold * (s.p : Real) := by positivity
  have htargetLower :
      (1 - p.epsilon / 2) * count * (s.p : Real) * threshold ≤
        (s.X.card : Real) := by
    calc
      (1 - p.epsilon / 2) * count * (s.p : Real) * threshold ≤
          (1 - p.ε') ^ 3 * (1 - p.latticeEta) *
            threshold * count * (s.p : Real) := by
        have h := mul_le_mul_of_nonneg_right hbase.1 hmult
        nlinarith
      _ ≤ (s.X.card : Real) := hlower
  have htargetUpper :
      (s.X.card : Real) ≤
        (1 + p.epsilon / 2) * count * (s.p : Real) * threshold := by
    calc
      (s.X.card : Real) ≤
          (1 + p.ε') ^ 3 * (1 + p.latticeEta) *
            threshold * count * (s.p : Real) := hupper
      _ ≤ (1 + p.epsilon / 2) * count * (s.p : Real) * threshold := by
        have h := mul_le_mul_of_nonneg_right hbase.2 hmult
        nlinarith
  have hestimate : (Est b threshold s : Real) =
      (s.X.card : Real) / ((s.p : Real) * threshold * scale) := by
    simp [Est, scale, Real.coe_toNNReal threshold hthreshold.le]
  rw [Arlib.mem_relErr, hestimate]
  constructor
  · change (1 - p.epsilon / 2) * ((count : Real) / scale) ≤
        (s.X.card : Real) / ((s.p : Real) * threshold * scale)
    rw [← mul_div_assoc]
    apply (div_le_div_iff₀ hscale hdenom).2
    calc
      ((1 - p.epsilon / 2) * count) * ((s.p : Real) * threshold * scale) =
          ((1 - p.epsilon / 2) * count * (s.p : Real) * threshold) * scale := by ring
      _ ≤ (s.X.card : Real) * scale :=
        mul_le_mul_of_nonneg_right htargetLower hscale.le
  · change (s.X.card : Real) / ((s.p : Real) * threshold * scale) ≤
        (1 + p.epsilon / 2) * ((count : Real) / scale)
    rw [← mul_div_assoc]
    apply (div_le_div_iff₀ hdenom hscale).2
    calc
      (s.X.card : Real) * scale ≤
          ((1 + p.epsilon / 2) * count * (s.p : Real) * threshold) * scale :=
        mul_le_mul_of_nonneg_right htargetUpper hscale.le
      _ = ((1 + p.epsilon / 2) * count) *
            ((s.p : Real) * threshold * scale) := by ring

end Kr25Ssmxt

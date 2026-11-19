import ttc.Analysis.MathlibCompat
import ttc.Analysis.TwoLoopCoinLaw
import ttc.Analysis.VolumeTrace

/-! The first thinning loop does not inspect or change the rate-dependent
Poisson mean through its coin outcomes. The pending count can therefore be
drawn independently of that loop's fair stream. -/

namespace ttc

open MeasureTheory ProbabilityTheory

theorem firstLoop_poisson_joint_law
    {n : Nat} (s : TTCState n) (intensity : NNReal)
    (threshold : Real) :
    (ttcReference.firstLoop s intensity threshold).bind (fun first =>
      (poissonMeasure (intensity * first.p)).map
        (Prod.mk first)) =
    (fairCoinStreamLaw.prod
      (poissonMeasure
        (intensity * (s.p /
          (2 : NNReal) ^ ttcReference.firstLoopExit s intensity threshold)))).map
      (fun pair =>
        (ttcReference.firstLoopResult s intensity threshold pair.1,
          pair.2)) := by
  let firstResult := ttcReference.firstLoopResult s intensity threshold
  let mean := intensity * (s.p /
    (2 : NNReal) ^ ttcReference.firstLoopExit s intensity threshold)
  let law : TTCState n → Measure Nat :=
    fun first => poissonMeasure (intensity * first.p)
  let K : TTCState n → Measure (TTCState n × Nat) :=
    fun first => (law first).map (Prod.mk first)
  have hrate : Measurable (fun first : TTCState n => first.p) := by
    exact measurable_fst.comp
      (comap_measurable
        (fun first : TTCState n =>
          (first.p, first.X, first.nextLabel)))
  have hlaw : Measurable law :=
    measurable_poissonMeasure.comp (measurable_const.mul hrate)
  have hK : Measurable K :=
    measurable_parametric_probability_map law hlaw (fun _ => inferInstance)
      (fun pair : TTCState n × Nat => pair) measurable_id
  have hfirst : Measurable firstResult :=
    measurable_rateThinningResult s intensity threshold
  change (fairCoinStreamLaw.map firstResult).bind K =
    (fairCoinStreamLaw.prod (poissonMeasure mean)).map
      (fun pair => (firstResult pair.1, pair.2))
  rw [bind_mapped_measure fairCoinStreamLaw firstResult hfirst K hK]
  have hmean (coins : Nat × Nat → Bool) :
      law (firstResult coins) = poissonMeasure mean := rfl
  change fairCoinStreamLaw.bind (fun coins =>
    (law (firstResult coins)).map (Prod.mk (firstResult coins))) = _
  simp_rw [hmean]
  rw [Measure.prod_eq_bind_map]
  have hout : Measurable
      (fun pair : (Nat × Nat → Bool) × Nat =>
        (firstResult pair.1, pair.2)) :=
    (hfirst.comp measurable_fst).prodMk measurable_snd
  rw [map_bind_measure fairCoinStreamLaw
    (fun coins : Nat × Nat → Bool =>
      (poissonMeasure mean).map (Prod.mk coins))
    (fun pair : (Nat × Nat → Bool) × Nat =>
      (firstResult pair.1, pair.2))
    (Measurable.map_prodMk_left.aemeasurable) hout]
  congr 1
  funext coins
  rw [Measure.map_map hout measurable_prodMk_left]
  rfl

end ttc

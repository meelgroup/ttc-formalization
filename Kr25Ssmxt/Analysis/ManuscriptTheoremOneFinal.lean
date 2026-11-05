import Kr25Ssmxt.Analysis.ManuscriptTheoremOneGivenOutcomes
import Kr25Ssmxt.Analysis.ManuscriptTTCVolumeConditioning
import Kr25Ssmxt.Analysis.ManuscriptConcreteVolumeGoodTrace
import Kr25Ssmxt.Analysis.ManuscriptFinalAccuracy

/-! Manuscript Theorem 1 for the current TTC program: integrate the
conditional estimate over the independent CV18 outcome vector. No `Prior`
hypothesis and no high-intensity regime premise. -/

namespace Kr25Ssmxt

open Classical MeasureTheory

theorem communityManuscriptComponentsGivenVolumes_list_congr
    {n k : Nat} (hn : 21 ≤ n) (prep : TTCPreprocessor n k)
    (b : Nat) (eta delta threshold : Real)
    (L₁ L₂ : List (PolytopeData n)) (h : L₁ = L₂)
    (outcomes : Fin L₂.length → VolumeOutcome) (state : TTCState n) :
    communityManuscriptComponentsGivenVolumes hn prep b eta delta threshold L₁
        (fun i => outcomes (Fin.cast (congrArg List.length h) i)) state =
      communityManuscriptComponentsGivenVolumes hn prep b eta delta threshold L₂
        outcomes state := by
  subst h
  rfl

theorem measurableSet_volumeOutcome_good {m : Nat}
    (good : Fin m → Set Real) (hgood : ∀ i, MeasurableSet (good i)) :
    MeasurableSet {o : Fin m → VolumeOutcome |
      ∀ i, (o i).1 = true ∧ ((o i).2 : Real) ∈ good i} := by
  have : {o : Fin m → VolumeOutcome |
      ∀ i, (o i).1 = true ∧ ((o i).2 : Real) ∈ good i} =
      ⋂ i, (fun o : Fin m → VolumeOutcome => o i) ⁻¹'
        ({v : VolumeOutcome | v.1 = true} ∩
          {v : VolumeOutcome | (v.2 : Real) ∈ good i}) := by
    ext o
    simp
  rw [this]
  refine MeasurableSet.iInter (fun i => (measurable_pi_apply i) ?_)
  refine MeasurableSet.inter ?_ ?_
  · exact measurable_fst (MeasurableSet.of_discrete (s := {true}))
  · exact (measurable_subtype_coe.comp measurable_snd) (hgood i)

set_option maxHeartbeats 4000000 in
/-- The manuscript TTC output achieves the intermediate `ε/2` estimate of the
scaled union lattice count with probability at least `1 - δ`. -/
theorem community_manuscriptTTC_lattice_estimate
    {n k : Nat} (hn : 21 ≤ n)
    (F : LRAFormula n k)
    (hbounded : Bornology.IsBounded (solutionSet F))
    (p : ApproxParams) (prep : TTCPreprocessor n k)
    (hm : 0 < (prep.run F hbounded).componentCount) :
    let D := prep.run F hbounded
    let b := (prep.choosePrecision D p).value
    (communityManuscriptTTC hn F hbounded p prep).real
      {estimate | (estimate : Real) ∈
        Arlib.relErr (p.epsilon / 2)
          ((D.latticePoints b).ncard / (10 : Real) ^ (b * n))} ≥
      1 - p.delta := by
  intro D b
  let m := D.componentCount
  let T := p.threshold m
  let eta := p.epsilonPrime
  let delta' := p.deltaPrime m
  let N := (D.latticePoints b).ncard
  let comps := communityManuscriptCertifiedComponents hn D p prep
  let components := List.ofFn D.component
  have hlist : comps.map (fun d => d.polytope) = components :=
    communityManuscriptCertifiedComponents_polytope hn D p prep
  have hlenC : components.length = comps.length := by
    rw [← hlist, List.length_map]
  let tr : Fin comps.length → Fin components.length := Fin.cast hlenC.symm
  let target : Set Real := Arlib.relErr (p.epsilon / 2)
    ((N : Real) / (10 : Real) ^ (b * n))
  let Bad : Set NNReal := {e | (e : Real) ∉ target}
  have hBad : MeasurableSet Bad :=
    (measurable_subtype_coe (measurableSet_Icc)).compl
  let law := communityManuscriptVolumeVectorLaw hn prep eta delta' components
  let K : (Fin components.length → VolumeOutcome) → Measure NNReal :=
    fun o => (communityManuscriptComponentsGivenVolumes hn prep b eta delta' T
      components o (TTCState.initial n)).map (manuscriptEstimate b T)
  have hTTC : communityManuscriptTTC hn F hbounded p prep = law.bind K :=
    communityManuscriptTTC_eq_volumeVector_bind hn F hbounded p prep
      (Nat.pos_iff_ne_zero.mp hm)
  let good : Set (Fin components.length → VolumeOutcome) :=
    {o | ∀ i, (o i).1 = true ∧
      ((o i).2 : Real) ∈ Arlib.relErr p.epsilonPrime
        (volume (components.get i).carrier).toReal}
  have hgoodMeas : MeasurableSet good :=
    measurableSet_volumeOutcome_good _ (fun _ => measurableSet_Icc)
  have hT : 0 < T := p.threshold_pos m
  have hvolumeU : ∀ P ∈ components, IsProbabilityMeasure
      ((communityManuscriptOracles hn prep).computeVolume P eta delta') := by
    intro P hP
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hP
    exact ((community_manuscript_volume_contract hn prep F hbounded p) i).1
  have hlawP : IsProbabilityMeasure law :=
    communityManuscriptVolumeVectorLaw_isProbabilityMeasure hn prep eta delta'
      components hvolumeU
  -- the CV18 outcome vector is good with probability at least 1 - δ/4
  have hvolumeC : ∀ P ∈ components, IsProbabilityMeasure
      ((communityManuscriptCostedOracles hn prep 1).computeVolumeWithCost
        P eta delta') := by
    intro P hP
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hP
    exact community_manuscript_costed_volume_isProbabilityMeasure hn D p prep 1 i
  have htrace := communityManuscript_components_volume_trace_good_accurate hn
    prep F hbounded p 1 hm
  have hmarg := communityManuscriptComponentsVolumeTrace_volume_marginal hn
    prep 1 b eta delta' T hT components hvolumeC (TTCState.initial n)
  have hlawGood : law.real good ≥ 1 - p.delta / 4 := by
    have hfst : Measurable (Prod.fst : (Fin components.length → VolumeOutcome) ×
        (TTCState n × Nat) → _) := measurable_fst
    have hl : law = _ := hmarg.symm
    rw [hl, map_measureReal_apply hfst hgoodMeas]
    exact htrace
  have hlawBad : law goodᶜ ≤ ENNReal.ofReal (p.delta / 4) := by
    rw [← ofReal_measureReal, measureReal_compl hgoodMeas, probReal_univ]
    apply ENNReal.ofReal_le_ofReal
    linarith
  -- conditional bound for each good outcome vector
  have hK : ∀ o, K o Bad ≤
      goodᶜ.indicator (1 : (Fin components.length → VolumeOutcome) → ENNReal) o +
      (ENNReal.ofReal (p.delta / 6) + ENNReal.ofReal (p.delta / 6)) := by
    intro o
    have _ := communityManuscriptComponentsGivenVolumes_isProbabilityMeasure hn
      prep b eta delta' T hT components o (TTCState.initial n)
    have hKo : K o Bad = (communityManuscriptComponentsGivenVolumes hn prep b
        eta delta' T components o (TTCState.initial n))
          ((manuscriptEstimate b T) ⁻¹' Bad) :=
      Measure.map_apply (measurable_manuscriptEstimate b T) hBad
    by_cases ho : o ∈ good
    · have hexec : communityManuscriptComponentsGivenVolumes hn prep b eta delta'
          T components o (TTCState.initial n) =
          (manuscriptOriginGivenVolumesLaw hn prep b eta delta' T comps
            (fun j => o (tr j)) (ManuscriptOriginConfiguration.initial n)).map
              (fun c => c.state) :=
        ((manuscriptOriginGivenVolumesLaw_map_state hn prep b eta delta' T hT
          comps (fun j => o (tr j)) (ManuscriptOriginConfiguration.initial n)).trans
          (communityManuscriptComponentsGivenVolumes_list_congr hn prep b eta
            delta' T _ components hlist o (TTCState.initial n))).symm
      have hlen := communityManuscriptCertifiedComponents_length hn D p prep
      have hgood' : ∀ i : Fin D.componentCount,
          ((fun j => o (tr j)) (Fin.cast hlen.symm i)).1 = true ∧
          (((fun j => o (tr j)) (Fin.cast hlen.symm i)).2 : Real) ∈
            Arlib.relErr p.epsilonPrime (volume (D.component i).carrier).toReal := by
        intro i
        have h := ho (tr (Fin.cast hlen.symm i))
        have hget : components.get (tr (Fin.cast hlen.symm i)) = D.component i := by
          change (List.ofFn D.component).get _ = _
          rw [List.get_ofFn]
          rfl
        rw [hget] at h
        exact h
      have hbound := communityManuscript_ghost_estimate_bad_le hn D p prep hm
        (fun j => o (tr j)) hgood'
      rw [hKo, hexec, Measure.map_apply measurable_manuscriptOriginConfiguration_state
        ((measurable_manuscriptEstimate b T) hBad)]
      exact hbound.trans le_add_self
    · have hind : goodᶜ.indicator (1 : (Fin components.length → VolumeOutcome) → ENNReal) o = 1 := by
        simp [Set.indicator, ho]
      rw [hind, hKo]
      exact prob_le_one.trans le_self_add
  have _ : IsProbabilityMeasure (communityManuscriptTTC hn F hbounded p prep) :=
    community_manuscriptTTC_isProbabilityMeasure hn F hbounded p prep
  have hKmeas : Measurable K := by
    have hcoords : Measurable
        (fun o : Fin components.length → VolumeOutcome =>
          (o, TTCState.initial n)) :=
      measurable_id.prodMk measurable_const
    have h := (measurable_communityManuscriptComponentsGivenVolumes hn prep b
      eta delta' T hT components).comp hcoords
    exact (Measure.measurable_map _ (measurable_manuscriptEstimate b T)).comp h
  have hTTCBad : (communityManuscriptTTC hn F hbounded p prep) Bad ≤
      ENNReal.ofReal (p.delta / 4) +
        (ENNReal.ofReal (p.delta / 6) + ENNReal.ofReal (p.delta / 6)) := by
    rw [hTTC]
    calc
      (law.bind K) Bad ≤ ∫⁻ o, K o Bad ∂law :=
        Measure.bind_apply_le hKmeas.aemeasurable hBad
      _ ≤ ∫⁻ o, (goodᶜ.indicator
          (1 : (Fin components.length → VolumeOutcome) → ENNReal) o +
          (ENNReal.ofReal (p.delta / 6) + ENNReal.ofReal (p.delta / 6))) ∂law :=
        lintegral_mono hK
      _ = law goodᶜ +
          (ENNReal.ofReal (p.delta / 6) + ENNReal.ofReal (p.delta / 6)) := by
        rw [lintegral_add_right _ measurable_const, lintegral_indicator_one
          hgoodMeas.compl, lintegral_const, measure_univ, mul_one]
      _ ≤ _ := by gcongr
  have hreal : (communityManuscriptTTC hn F hbounded p prep).real Bad ≤
      p.delta / 4 + (p.delta / 6 + p.delta / 6) := by
    have hd := p.delta_pos
    rw [← ENNReal.ofReal_add (by positivity) (by positivity),
      ← ENNReal.ofReal_add (by positivity) (by positivity)] at hTTCBad
    unfold Measure.real
    exact (ENNReal.toReal_le_of_le_ofReal (by positivity) hTTCBad)
  have hset : {estimate : NNReal | (estimate : Real) ∈ target} = Badᶜ := by
    ext e
    simp [Bad]
  change (communityManuscriptTTC hn F hbounded p prep).real
    {estimate : NNReal | (estimate : Real) ∈ target} ≥ 1 - p.delta
  rw [hset, measureReal_compl hBad, probReal_univ]
  linarith [p.delta_pos]

/-- **Manuscript Theorem 1** for the current TTC program
(`communityManuscriptTTC`): with the concrete CV18 and Hit-and-Run/KV97
oracles, the output is an `ε`-relative estimate of the volume of the
existentially projected solution set with probability at least `1 - δ`.
There is no `Prior` hypothesis and no regime premise. -/
theorem community_manuscriptTTC_volume_accuracy
    {n k : Nat} (hn : 21 ≤ n)
    (F : LRAFormula n k)
    (hbounded : Bornology.IsBounded (solutionSet F))
    (p : ApproxParams) (prep : TTCPreprocessor n k) :
    (communityManuscriptTTC hn F hbounded p prep).real
      {estimate | (estimate : Real) ∈
        Arlib.relErr p.epsilon (volume (solutionSet F)).toReal} ≥
      1 - p.delta := by
  by_cases hempty : (prep.run F hbounded).componentCount = 0
  · exact community_manuscriptTTC_volume_accuracy_empty hn F hbounded p prep
      hempty
  · exact community_manuscriptTTC_volume_accuracy_of_lattice_estimate hn F
      hbounded p prep
      (community_manuscriptTTC_lattice_estimate hn F hbounded p prep
        (Nat.pos_of_ne_zero hempty))

end Kr25Ssmxt

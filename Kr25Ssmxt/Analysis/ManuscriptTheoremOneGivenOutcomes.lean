import Kr25Ssmxt.Analysis.PrecisionChoice
import Kr25Ssmxt.Analysis.PrecisionRequirements
import Kr25Ssmxt.Analysis.ManuscriptTheoremOneCrossing
import Kr25Ssmxt.Analysis.ManuscriptOriginStepsCertified
import Kr25Ssmxt.Analysis.ManuscriptConcreteSourceProduct
import Kr25Ssmxt.Analysis.ManuscriptEstimateFromCount
import Kr25Ssmxt.Analysis.ManuscriptNoUndueFirstHalving
import Kr25Ssmxt.Analysis.ManuscriptDyadicChernoffSum
import Kr25Ssmxt.Analysis.ManuscriptRunMarginal

/-! Conditional on successful CV18 outcomes, the ghost run's final estimate
fails the intermediate lattice-count guarantee with probability at most
`δ/6 + δ/6`. -/

namespace Kr25Ssmxt

open Classical MeasureTheory

/-- The window outside of which the fixed-level Chernoff bound applies. -/
def manuscriptBadWindow (p : ApproxParams) (m count level : Nat) : Set Nat :=
  {j : Nat |
    (j : Real) < (1 - p.ε') * (count : Real) *
      (Real.toNNReal (p.Thresh m * (1 - p.ε') ^ 2 *
        (1 - p.latticeEta) * (1 / (2 : NNReal) ^ level : NNReal)) : Real) ∨
    (1 + p.ε') * (count : Real) *
      (Real.toNNReal (p.Thresh m * (1 + p.ε') ^ 2 *
        (1 + p.latticeEta) * (1 / (2 : NNReal) ^ level : NNReal)) : Real) <
      (j : Real)}

theorem ApproxParams.epsilonPrime_lt_one (p : ApproxParams) :
    p.ε' < 1 := by
  dsimp [ApproxParams.ε']
  linarith [p.epsilon_le_one]

theorem ApproxParams.latticeEta_lt_one (p : ApproxParams) :
    p.latticeEta < 1 := by
  dsimp [ApproxParams.latticeEta]
  linarith [p.epsilon_le_one]

theorem ApproxParams.epsilonPrime_pos' (p : ApproxParams) :
    0 < p.ε' := by
  dsimp [ApproxParams.ε']
  linarith [p.epsilon_pos]

theorem ApproxParams.latticeEta_pos' (p : ApproxParams) :
    0 < p.latticeEta := by
  dsimp [ApproxParams.latticeEta]
  linarith [p.epsilon_pos]

/-- A stored population inside the fixed-level window at the final level
gives the manuscript's `ε/2` estimate of the scaled lattice count. -/
theorem manuscriptEstimate_of_not_badWindow
    {n : Nat} (s : TTCState n) (b count m level : Nat) (p : ApproxParams)
    (hrate : s.p = 1 / (2 : NNReal) ^ level)
    (hwin : s.X.card ∉ manuscriptBadWindow p m count level) :
    (Est b (p.Thresh m) s : Real) ∈
      Arlib.relErr (p.epsilon / 2)
        ((count : Real) / (10 : Real) ^ (b * n)) := by
  have hT := p.threshold_pos m
  have he1 := p.epsilonPrime_lt_one
  have hl1 := p.latticeEta_lt_one
  have he0 := p.epsilonPrime_pos'
  have hl0 := p.latticeEta_pos'
  have hrateR : (s.p : Real) = 1 / (2 : Real) ^ level := by
    rw [hrate]
    push_cast
    rfl
  have hratePos : 0 < (s.p : Real) := by
    rw [hrateR]
    positivity
  have hrate' : (((1 / (2 : NNReal) ^ level : NNReal)) : Real) =
      (s.p : Real) := by
    rw [hrate]
  have hlowerNN : (Real.toNNReal (p.Thresh m * (1 - p.ε') ^ 2 *
      (1 - p.latticeEta) * (1 / (2 : NNReal) ^ level : NNReal)) : Real) =
      p.Thresh m * (1 - p.ε') ^ 2 * (1 - p.latticeEta) *
        (s.p : Real) := by
    rw [Real.coe_toNNReal _ (by
      have : 0 ≤ 1 - p.latticeEta := by linarith
      positivity), hrate']
  have hupperNN : (Real.toNNReal (p.Thresh m * (1 + p.ε') ^ 2 *
      (1 + p.latticeEta) * (1 / (2 : NNReal) ^ level : NNReal)) : Real) =
      p.Thresh m * (1 + p.ε') ^ 2 * (1 + p.latticeEta) *
        (s.p : Real) := by
    rw [Real.coe_toNNReal _ (by positivity), hrate']
  simp only [manuscriptBadWindow, Set.mem_setOf_eq, not_or, not_lt,
    hlowerNN, hupperNN] at hwin
  apply manuscriptEstimate_of_population_envelope s b count p (p.Thresh m)
    hT hratePos
  · nlinarith [hwin.1]
  · nlinarith [hwin.2]

theorem manuscriptOriginGivenVolumesLaw_refreshLaw_bind_of_ne_nil
    {n k : Nat} (hn : 21 ≤ n) (prep : TTCPreprocessor n k)
    (b : Nat) (eta delta threshold : Real) (hthreshold : 0 < threshold)
    (components : List
      (ManuscriptOriginCertifiedComponent n k hn prep b eta delta))
    (hne : components ≠ [])
    (outcomes : Fin components.length → VolumeOutcome)
    (c : ManuscriptOriginConfiguration n) :
    c.refreshLaw.bind (manuscriptOriginGivenVolumesLaw hn prep b eta delta
        threshold components outcomes) =
      manuscriptOriginGivenVolumesLaw hn prep b eta delta threshold
        components outcomes c := by
  cases components with
  | nil => exact absurd rfl hne
  | cons d rest =>
      exact manuscriptOriginGivenVolumesLaw_refreshLaw_bind hn prep b eta
        delta threshold hthreshold d rest outcomes c

theorem list_get_ofFn_map_eq {α β : Type*} {m : Nat} (f : Fin m → α)
    (proj : α → β) (g : Fin m → β) (hfg : ∀ j, proj (f j) = g j)
    (i : Fin (List.ofFn f).length) :
    proj ((List.ofFn f).get i) = g (Fin.cast List.length_ofFn i) := by
  rw [List.get_ofFn, hfg]

theorem communityManuscriptCertifiedComponents_get_polytope
    {n k : Nat} (hn : 21 ≤ n) {F : LRAFormula n k}
    (D : Decomposition F) (p : ApproxParams) (prep : TTCPreprocessor n k)
    (i : Fin (communityManuscriptCertifiedComponents hn D p prep).length) :
    ((communityManuscriptCertifiedComponents hn D p prep).get i).polytope =
      D.component (Fin.cast
        (communityManuscriptCertifiedComponents_length hn D p prep) i) := by
  exact list_get_ofFn_map_eq _ (fun d => d.polytope) D.component
    (fun _ => rfl) i

theorem communityManuscriptCertifiedComponents_support
    {n k : Nat} (hn : 21 ≤ n) {F : LRAFormula n k}
    (D : Decomposition F) (p : ApproxParams) (prep : TTCPreprocessor n k) :
    let b := (prep.choosePrecision D p).value
    let S := (D.codedUnion_finite (by omega) p b
      (prep.choosePrecision D p).adequate).toFinset
    ∀ d ∈ communityManuscriptCertifiedComponents hn D p prep,
      (normalizedHitAndRunPointLaw hn d.polytope b d.route.1 p.ε'
        d.route.2.1 d.route.2.2.1 d.route.2.2.2.1 d.route.2.2.2.2)
        (S : Set (LatticePoint n))ᶜ = 0 := by
  intro b S d hd
  unfold communityManuscriptCertifiedComponents at hd
  obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hd
  exact communityManuscriptPointLaw_support_codedUnion hn D p b
    (prep.choosePrecision D p).adequate i

set_option maxHeartbeats 4000000 in
/-- **Conditional Theorem 1.** For successful clipped CV18 outcomes, the
ghost run's final estimate misses the `ε/2` scaled-lattice guarantee with
probability at most `δ/6 + δ/6`. -/
theorem communityManuscript_ghost_estimate_bad_le
    {n k : Nat} (hn : 21 ≤ n) {F : LRAFormula n k}
    (D : Decomposition F) (p : ApproxParams) (prep : TTCPreprocessor n k)
    (hm : 0 < D.componentCount)
    (outcomes : Fin (communityManuscriptCertifiedComponents hn D p prep).length →
      VolumeOutcome)
    (hgood : ∀ i : Fin D.componentCount,
      (outcomes (Fin.cast
        (communityManuscriptCertifiedComponents_length hn D p prep).symm i)).1 =
          true ∧
      ((outcomes (Fin.cast
        (communityManuscriptCertifiedComponents_length hn D p prep).symm i)).2 :
          Real) ∈ Arlib.relErr p.ε'
            (volume (D.component i).carrier).toReal) :
    let b := (prep.choosePrecision D p).value
    (manuscriptOriginGivenVolumesLaw hn prep b p.ε'
      (p.δ' D.componentCount) (p.Thresh D.componentCount)
      (communityManuscriptCertifiedComponents hn D p prep) outcomes
      (ManuscriptOriginConfiguration.initial n))
      {c | (Est b (p.Thresh D.componentCount) c.state : Real) ∉
        Arlib.relErr (p.epsilon / 2)
          (((D.latticePoints b).ncard : Real) / (10 : Real) ^ (b * n))} ≤
      ENNReal.ofReal (p.delta / 6) + ENNReal.ofReal (p.delta / 6) := by
  intro b
  let hprec := (prep.choosePrecision D p).adequate
  let m := D.componentCount
  let T := p.Thresh m
  let eta := p.ε'
  let S := (D.codedUnion_finite (by omega) p b hprec).toFinset
  let comps := communityManuscriptCertifiedComponents hn D p prep
  let N := (D.latticePoints b).ncard
  let level0 := manuscriptDyadicCutoff N - 1
  let hlen := communityManuscriptCertifiedComponents_length hn D p prep
  let o' : Fin m → VolumeOutcome := fun i => outcomes (Fin.cast hlen.symm i)
  let G := manuscriptOriginGivenVolumesLaw hn prep b eta (p.δ' m) T
    comps outcomes
  let μ0 := (ManuscriptOriginConfiguration.initial n).refreshLaw
  have hT : 0 < T := p.threshold_pos m
  have _ : IsProbabilityMeasure μ0 :=
    (ManuscriptOriginConfiguration.initial n).refreshLaw_isProbabilityMeasure
  have hG : Measurable G :=
    measurable_manuscriptOriginGivenVolumesLaw hn prep b eta (p.δ' m)
      T hT comps outcomes
  have hne : comps ≠ [] := by
    intro h
    have hl : comps.length = m := hlen
    rw [h] at hl
    simp at hl
    omega
  have hν : G (ManuscriptOriginConfiguration.initial n) = μ0.bind G :=
    (manuscriptOriginGivenVolumesLaw_refreshLaw_bind_of_ne_nil hn prep b eta
      (p.δ' m) T hT comps hne outcomes _).symm
  have hstat0 : μ0.bind (fun c => c.refreshLaw) = μ0 :=
    (ManuscriptOriginConfiguration.initial n).refreshLaw_idempotent
  have hM : MeasurableSet {c : ManuscriptOriginConfiguration n | c.MarksIn S} :=
    measurableSet_manuscriptOriginMarksIn S
  have hmarks0 : ∀ᵐ c ∂μ0, c.MarksIn S := by
    apply ae_map_of_ae_marksIn
      (ManuscriptOriginConfiguration.initial n).measurable_refreshFuture.aemeasurable hM
    refine Filter.Eventually.of_forall (fun future => ?_)
    intro tag htag
    simp [ManuscriptOriginConfiguration.refreshFuture,
      ManuscriptOriginConfiguration.initial,
      ManuscriptOriginSourceState.initial] at htag
  have hsupport := communityManuscriptCertifiedComponents_support hn D p prep
  have hmarksν : ∀ᵐ c ∂(μ0.bind G), c.MarksIn S :=
    manuscriptOriginGivenVolumesLaw_ae_marksIn hn prep b eta (p.δ' m)
      T hT S comps hsupport outcomes μ0 hmarks0
  -- fixed-level count laws
  have hcounts : ∀ level : Nat, (μ0.bind G).map
      (fun c : ManuscriptOriginConfiguration n => c.source.pointCounts level S) =
      fixedLevelLaw (manuscriptCertifiedFixedLevelSteps D b S T
        (fun i => (o' i).2) (communityManuscriptPointLaw hn D p b hprec)
        (1 / (2 : NNReal) ^ level))
        (Measure.pi (fun _ : S => ProbabilityTheory.poissonMeasure 0)) := by
    intro level
    rw [manuscriptOriginGivenVolumesLaw_fixedLevel hn prep b eta (p.δ' m)
      T hT S level comps hsupport outcomes μ0 hstat0,
      manuscriptOrigin_initial_refreshLaw_pointCounts level S,
      communityManuscript_givenVolumesSteps_eq_certified hn D p prep S level
        outcomes]
  have hgood' : ∀ i : Fin m, (o' i).1 = true ∧
      ((o' i).2 : Real) ∈ Arlib.relErr p.ε'
        (volume (D.component i).carrier).toReal := hgood
  let pi0 : Measure (S → Nat) :=
    Measure.pi (fun _ : S => ProbabilityTheory.poissonMeasure 0)
  have hsumMeas : Measurable (fun v : S → Nat => ∑ x, v x) :=
    Measurable.of_discrete
  have hfin : ∀ pfx : List (FixedLevelStep S),
      IsFiniteMeasure ((fixedLevelLaw pfx pi0).map (fun v : S → Nat => ∑ x, v x)) := by
    intro pfx
    have h := fixedLevelLaw_zero_poisson_prefix S pfx
    change fixedLevelLaw pfx pi0 = _ at h
    rw [h]
    infer_instance
  -- crossing the penultimate cutoff
  let full := manuscriptCertifiedFixedLevelSteps D b S T (fun i => (o' i).2)
    (communityManuscriptPointLaw hn D p b hprec) (1 / (2 : NNReal) ^ level0)
  let Bud : ENNReal := ENNReal.ofReal (p.delta / (6 * m))
  have hbudget : ∀ pfx : List (FixedLevelStep S), (∀ s ∈ pfx, s ∈ full) →
      ((fixedLevelLaw pfx pi0).map (fun v : S → Nat => ∑ x, v x))
        {j : Nat | T ≤ (j : Real)} ≤ Bud := by
    intro pfx hpfx
    have h := communityManuscriptFixedLevel_cutoff_prefix_budget hn D p b hprec
      hm o' hgood' pfx hpfx
    have _ := hfin pfx
    rw [← ofReal_measureReal]
    exact ENNReal.ofReal_le_ofReal h
  have hsteps : ∀ s ∈ manuscriptOriginGivenVolumesSteps hn prep b eta
      (p.δ' m) T S level0 comps outcomes, s ∈ full := by
    intro s hs
    rw [communityManuscript_givenVolumesSteps_eq_certified hn D p prep S level0
      outcomes] at hs
    exact hs
  have hnocross : ∀ i : Fin comps.length,
      ∀ c : ManuscriptOriginConfiguration n, c.level ≤ level0 →
        c.level + manuscriptRateExit
          (c.state.removeComponent (comps.get i).polytope)
          (ttc.t b n T (outcomes i).2) T ≤ level0 := by
    intro i c hc
    rw [communityManuscriptCertifiedComponents_get_polytope hn D p prep i]
    have hidx : Fin.cast hlen.symm (Fin.cast hlen i) = i := Fin.ext rfl
    have hv := (hgood (Fin.cast hlen i)).2
    rw [hidx] at hv
    have h := manuscript_no_first_halving_past_cutoff (by omega) D p b hprec hm
      (Fin.cast hlen i) (outcomes i).2 hv
      (c.state.removeComponent (D.component (Fin.cast hlen i))) c.level hc
      c.p
    change _ ≤ manuscriptDyadicCutoff N - 1 - c.level at h
    change c.level ≤ manuscriptDyadicCutoff N - 1 at hc
    refine le_trans (Nat.add_le_add_left h c.level) ?_
    omega
  have hcounts0 : μ0.map (fun c : ManuscriptOriginConfiguration n =>
      c.source.pointCounts level0 S) = fixedLevelLaw [] pi0 :=
    manuscriptOrigin_initial_refreshLaw_pointCounts level0 S
  have hcross := manuscriptOriginGivenVolumesLaw_crossing hn prep b eta
    (p.δ' m) T hT S level0 full Bud hbudget comps hsupport outcomes
    hsteps hnocross μ0 hstat0 hmarks0 [] (by simp) hcounts0
  have hA0 : μ0 {c : ManuscriptOriginConfiguration n | level0 < c.level} = 0 := by
    change ((Measure.infinitePi (fun _ : Nat × (Nat × Nat) => fairCoinLaw)).map
      (ManuscriptOriginConfiguration.initial n).refreshFuture) _ = 0
    have hmeasA : MeasurableSet
        {c : ManuscriptOriginConfiguration n | level0 < c.level} :=
      measurable_manuscriptOriginConfiguration_level
        (MeasurableSet.of_discrete (s := {j : Nat | level0 < j}))
    rw [Measure.map_apply
      (ManuscriptOriginConfiguration.initial n).measurable_refreshFuture hmeasA]
    have hempty : (ManuscriptOriginConfiguration.initial n).refreshFuture ⁻¹'
        {c : ManuscriptOriginConfiguration n | level0 < c.level} = ∅ := by
      ext future
      simp [ManuscriptOriginConfiguration.refreshFuture,
        ManuscriptOriginConfiguration.initial]
    rw [hempty, measure_empty]
  have hlenm : (comps.length : ENNReal) = m := by
    exact_mod_cast hlen
  have hA : (μ0.bind G) {c | level0 < c.level} ≤ ENNReal.ofReal (p.delta / 6) := by
    refine hcross.trans ?_
    rw [hA0, zero_add, hlenm]
    have hmpos : (0 : Real) < m := by exact_mod_cast hm
    rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (by positivity)]
    apply ENNReal.ofReal_le_ofReal
    rw [le_iff_eq_or_lt]
    left
    field_simp
  -- levelwise Chernoff
  let a := (1 - p.ε') * p.ε' ^ 2 * T / 24
  let E : Nat → Set (ManuscriptOriginConfiguration n) := fun level =>
    {c | (∑ x : S, c.source.pointCounts level S x) ∈
      manuscriptBadWindow p m N level}
  have hE : ∀ level ≤ level0, (μ0.bind G) (E level) ≤
      ENNReal.ofReal (2 * Real.exp (-a * (2 : Real) ^ (level0 - level))) := by
    intro level hlevel
    have hcountMeas : Measurable (fun c : ManuscriptOriginConfiguration n =>
        c.source.pointCounts level S) :=
      (measurable_manuscriptOriginSourceState_pointCounts level S).comp
        measurable_manuscriptOriginConfiguration_source
    have hset : E level = (fun c : ManuscriptOriginConfiguration n =>
        c.source.pointCounts level S) ⁻¹'
        ((fun v : S → Nat => ∑ x, v x) ⁻¹' manuscriptBadWindow p m N level) :=
      rfl
    rw [hset, ← Measure.map_apply hcountMeas
      (hsumMeas (MeasurableSet.of_discrete)), hcounts level,
      ← Measure.map_apply hsumMeas (MeasurableSet.of_discrete)]
    have h := communityManuscriptFixedLevel_error_bound hn D p b hprec hm o'
      hgood' level hlevel
    have _ := hfin (manuscriptCertifiedFixedLevelSteps D b S T
      (fun i => (o' i).2) (communityManuscriptPointLaw hn D p b hprec)
      (1 / (2 : NNReal) ^ level))
    rw [← ofReal_measureReal]
    exact ENNReal.ofReal_le_ofReal h
  have hsum : (∑ level ∈ Finset.range (level0 + 1), (μ0.bind G) (E level)) ≤
      ENNReal.ofReal (p.delta / 6) := by
    calc
      (∑ level ∈ Finset.range (level0 + 1), (μ0.bind G) (E level)) ≤
          ∑ level ∈ Finset.range (level0 + 1),
            ENNReal.ofReal (2 * Real.exp (-a * (2 : Real) ^ (level0 - level))) := by
        apply Finset.sum_le_sum
        intro level hlevel
        exact hE level (Nat.lt_succ_iff.mp (Finset.mem_range.mp hlevel))
      _ = ENNReal.ofReal (∑ level ∈ Finset.range (level0 + 1),
            2 * Real.exp (-a * (2 : Real) ^ (level0 - level))) := by
        rw [ENNReal.ofReal_sum_of_nonneg]
        intro level _
        positivity
      _ ≤ ENNReal.ofReal (p.delta / 6) :=
        ENNReal.ofReal_le_ofReal (p.dyadic_chernoff_budget m level0)
  -- union bound
  have hsub : ∀ᵐ c ∂(μ0.bind G),
      c ∈ {c : ManuscriptOriginConfiguration n |
        (Est b T c.state : Real) ∉
          Arlib.relErr (p.epsilon / 2) ((N : Real) / (10 : Real) ^ (b * n))} →
      c ∈ {c | level0 < c.level} ∪
        ⋃ level ∈ Finset.range (level0 + 1), E level := by
    filter_upwards [hmarksν] with c hc hbad
    by_cases hl : level0 < c.level
    · exact Or.inl hl
    · right
      apply Set.mem_biUnion (Finset.mem_range.mpr
        (Nat.lt_succ_of_le (Nat.le_of_not_lt hl)))
      by_contra hnot
      apply hbad
      have hcard := c.samples_card_eq_sum_pointCounts S hc
      apply manuscriptEstimate_of_not_badWindow c.state b N m c.level p c.p
      rw [hcard]
      exact hnot
  show G (ManuscriptOriginConfiguration.initial n) _ ≤ _
  rw [hν]
  calc
    (μ0.bind G) {c | (Est b T c.state : Real) ∉
        Arlib.relErr (p.epsilon / 2) ((N : Real) / (10 : Real) ^ (b * n))} ≤
        (μ0.bind G) ({c | level0 < c.level} ∪
          ⋃ level ∈ Finset.range (level0 + 1), E level) :=
      measure_mono_ae hsub
    _ ≤ (μ0.bind G) {c | level0 < c.level} +
        (μ0.bind G) (⋃ level ∈ Finset.range (level0 + 1), E level) :=
      measure_union_le _ _
    _ ≤ ENNReal.ofReal (p.delta / 6) + ENNReal.ofReal (p.delta / 6) := by
      gcongr
      exact (measure_biUnion_finset_le _ _).trans hsum

end Kr25Ssmxt

import Kr25Ssmxt.Analysis.ManuscriptOriginCrossing
import Kr25Ssmxt.Analysis.ManuscriptOriginGivenVolumesState

/-! Crossing the penultimate dyadic cutoff during the ghost fold is charged,
component by component, to the fixed-level upper-tail event at the cutoff. -/

namespace Kr25Ssmxt

open Classical MeasureTheory

theorem fixedLevelLaw_append {ι : Type*} [Fintype ι] [DecidableEq ι]
    (pre post : List (FixedLevelStep ι)) (μ : Measure (ι → Nat)) :
    fixedLevelLaw (pre ++ post) μ = fixedLevelLaw post (fixedLevelLaw pre μ) := by
  induction pre generalizing μ with
  | nil => rfl
  | cons s rest ih => exact ih _

/-- Every property satisfied by all refreshed advance outputs holds almost
surely under the refreshed component law. -/
theorem manuscriptOriginRefreshedComponentLaw_ae_of_forall
    {n : Nat} (hn : 21 ≤ n) (P : PolytopeData n)
    (b : Nat) (eta threshold : Real) (hthreshold : 0 < threshold)
    (hroute : 1 ≤ decimalScale b * P.inradius ∧
      0 < eta ∧ eta ≤ 1 ∧
      (codedLatticePoints P b).Finite ∧
      (codedLatticePoints P b).Nonempty)
    (intensity : NNReal) (c : ManuscriptOriginConfiguration n)
    {q : ManuscriptOriginConfiguration n → Prop}
    (hq : MeasurableSet {c' | q c'})
    (hall : ∀ (future : Nat × (Nat × Nat) → Bool) (basePending : Nat)
      (preCoins fresh : Nat × Nat → Bool) (tape : Nat → LatticePoint n),
      q ((c.refreshFuture future).advance P intensity threshold basePending
        preCoins fresh tape)) :
    ∀ᵐ c' ∂(manuscriptOriginRefreshedComponentLaw hn P b eta threshold
      hroute intensity c), q c' := by
  rw [manuscriptOriginRefreshedComponentLaw_eq_source hn P b eta threshold
    hthreshold hroute intensity c]
  apply ae_bind_of_ae_ae_marksIn
    ((measurable_manuscriptOriginPoissonCoinTapeLaw hn P b eta threshold
      hthreshold hroute intensity).comp c.measurable_refreshFuture).aemeasurable hq
  refine Filter.Eventually.of_forall (fun future => ?_)
  unfold manuscriptOriginPoissonCoinTapeLaw
  apply ae_bind_of_ae_ae_marksIn (measurable_of_countable _).aemeasurable hq
  refine Filter.Eventually.of_forall (fun basePending => ?_)
  unfold manuscriptOriginFairCoinTapeLaw
  apply ae_bind_of_ae_ae_marksIn
    ((measurable_manuscriptOriginCoinPairTapeLaw hn P b eta threshold
      hthreshold hroute intensity basePending).comp
        (measurable_const.prodMk measurable_id)).aemeasurable hq
  refine Filter.Eventually.of_forall (fun coins => ?_)
  unfold manuscriptOriginCoinPairTapeLaw
  apply ae_map_of_ae_marksIn
    ((c.refreshFuture future).measurable_advance_tape P intensity threshold
      basePending coins.1 coins.2).aemeasurable hq
  exact Filter.Eventually.of_forall (fun tape =>
    hall future basePending coins.1 coins.2 tape)

theorem measurable_manuscriptOriginTotalCount {n : Nat}
    (level : Nat) (S : Finset (LatticePoint n)) :
    Measurable (fun c : ManuscriptOriginConfiguration n =>
      ∑ x : S, c.source.pointCounts level S x) := by
  have hcounts : Measurable (fun c : ManuscriptOriginConfiguration n =>
      c.source.pointCounts level S) :=
    (measurable_manuscriptOriginSourceState_pointCounts level S).comp
      measurable_manuscriptOriginConfiguration_source
  have hsum : Measurable (fun v : S → Nat => ∑ x, v x) :=
    Measurable.of_discrete
  exact hsum.comp hcounts

/-- One refreshed component step. -/
theorem manuscriptOrigin_refreshed_step_crossing
    {n : Nat} (hn : 21 ≤ n) (P : PolytopeData n)
    (b : Nat) (eta threshold : Real) (hthreshold : 0 < threshold)
    (hroute : 1 ≤ decimalScale b * P.inradius ∧
      0 < eta ∧ eta ≤ 1 ∧
      (codedLatticePoints P b).Finite ∧
      (codedLatticePoints P b).Nonempty)
    (intensity : NNReal) (S : Finset (LatticePoint n))
    (hsupport : (normalizedHitAndRunPointLaw hn P b hroute.1 eta
      hroute.2.1 hroute.2.2.1 hroute.2.2.2.1 hroute.2.2.2.2)
        (S : Set (LatticePoint n))ᶜ = 0)
    (level0 : Nat)
    (hnocross : ∀ c : ManuscriptOriginConfiguration n, c.level ≤ level0 →
      c.level + ttcPseudocode.firstLoopExit (c.state.removeComponent P) intensity
        threshold ≤ level0)
    (μ : Measure (ManuscriptOriginConfiguration n))
    (hmarks : ∀ᵐ c ∂μ, c.MarksIn S) :
    (μ.bind (manuscriptOriginRefreshedComponentLaw hn P b eta threshold
        hroute intensity)) {c | level0 < c.level} ≤
      μ {c | level0 < c.level} +
        (μ.bind (manuscriptOriginRefreshedComponentLaw hn P b eta threshold
          hroute intensity))
          {c | threshold ≤ ((∑ x : S, c.source.pointCounts level0 S x : Nat) :
            Real)} := by
  let R := manuscriptOriginRefreshedComponentLaw hn P b eta threshold hroute
    intensity
  have hR : Measurable R :=
    measurable_manuscriptOriginRefreshedComponentLaw hn P b eta threshold
      hthreshold hroute intensity
  let A : Set (ManuscriptOriginConfiguration n) := {c | level0 < c.level}
  let B : Set (ManuscriptOriginConfiguration n) :=
    {c | threshold ≤ ((∑ x : S, c.source.pointCounts level0 S x : Nat) : Real)}
  have hA : MeasurableSet A :=
    measurable_manuscriptOriginConfiguration_level
      (MeasurableSet.of_discrete (s := {k : Nat | level0 < k}))
  have hB : MeasurableSet B :=
    measurable_manuscriptOriginTotalCount level0 S
      (MeasurableSet.of_discrete
        (s := {k : Nat | threshold ≤ (k : Real)}))
  have hM : MeasurableSet {c : ManuscriptOriginConfiguration n | c.MarksIn S} :=
    measurableSet_manuscriptOriginMarksIn S
  have hpoint : ∀ c, c.MarksIn S → R c A ≤ A.indicator 1 c + R c B := by
    intro c hc
    let _ := manuscriptOriginRefreshedComponentLaw_isProbabilityMeasure hn P
      b eta threshold hthreshold hroute intensity c
    by_cases hlev : level0 < c.level
    · have h1 : R c A ≤ 1 := prob_le_one
      have hind : A.indicator 1 c = (1 : ENNReal) := by
        simp [A, Set.indicator, hlev]
      rw [hind]
      exact h1.trans le_self_add
    · have hle : c.level ≤ level0 := Nat.le_of_not_lt hlev
      have hgood : ∀ᵐ c' ∂R c, c'.MarksIn S → c' ∈ A → c' ∈ B := by
        apply manuscriptOriginRefreshedComponentLaw_ae_of_forall hn P b eta
          threshold hthreshold hroute intensity c
          (by
            have h := (hM.compl.union hA.compl).union hB
            convert h using 1
            ext c'
            simp only [Set.mem_setOf_eq, Set.mem_union, Set.mem_compl_iff, A, B]
            tauto)
        intro future basePending preCoins fresh tape hmk hcross
        exact (c.refreshed_advance_crossing P intensity threshold basePending
          preCoins fresh future tape level0 (hnocross c hle) hcross S hmk).le
      have hmk : ∀ᵐ c' ∂R c, c'.MarksIn S :=
        manuscriptOriginRefreshedComponentLaw_ae_marksIn hn P b eta threshold
          hthreshold hroute intensity S hsupport c hc
      have hsub : R c A ≤ R c B := by
        apply measure_mono_ae
        filter_upwards [hgood, hmk] with c' h1 h2 h3
        exact h1 h2 h3
      exact hsub.trans le_add_self
  calc
    (μ.bind R) A = ∫⁻ c, R c A ∂μ := Measure.bind_apply hA hR.aemeasurable
    _ ≤ ∫⁻ c, (A.indicator 1 c + R c B) ∂μ := by
      apply lintegral_mono_ae
      filter_upwards [hmarks] with c hc
      exact hpoint c hc
    _ = ∫⁻ c, A.indicator 1 c ∂μ + ∫⁻ c, R c B ∂μ := by
      rw [lintegral_add_left]
      exact (measurable_one.indicator hA)
    _ = μ A + (μ.bind R) B := by
      rw [lintegral_indicator_one hA, Measure.bind_apply hB hR.aemeasurable]

set_option maxHeartbeats 2000000 in
/-- Across the whole ghost fold, the probability of ending above `level0`
is at most the initial probability plus one cutoff budget per component. -/
theorem manuscriptOriginGivenVolumesLaw_crossing
    {n k : Nat} (hn : 21 ≤ n) (prep : TTCPreprocessor n k)
    (b : Nat) (eta delta threshold : Real) (hthreshold : 0 < threshold)
    (S : Finset (LatticePoint n)) (level0 : Nat)
    (full : List (FixedLevelStep S)) (B : ENNReal)
    (hbudget : ∀ pfx : List (FixedLevelStep S), (∀ s ∈ pfx, s ∈ full) →
      ((fixedLevelLaw pfx
        (Measure.pi (fun _ : S => ProbabilityTheory.poissonMeasure 0))).map
          (fun v : S → Nat => ∑ x, v x)) {j : Nat | threshold ≤ (j : Real)} ≤ B)
    (components : List
      (ManuscriptOriginCertifiedComponent n k hn prep b eta delta))
    (hsupport : ∀ d ∈ components,
      (normalizedHitAndRunPointLaw hn d.polytope b d.route.1 eta
        d.route.2.1 d.route.2.2.1 d.route.2.2.2.1 d.route.2.2.2.2)
        (S : Set (LatticePoint n))ᶜ = 0)
    (outcomes : Fin components.length → VolumeOutcome)
    (hsteps : ∀ s ∈ manuscriptOriginGivenVolumesSteps hn prep b eta delta
      threshold S level0 components outcomes, s ∈ full)
    (hnocross : ∀ i : Fin components.length,
      ∀ c : ManuscriptOriginConfiguration n, c.level ≤ level0 →
        c.level + ttcPseudocode.firstLoopExit
          (c.state.removeComponent (components.get i).polytope)
          (ttcPseudocode.t b n threshold (outcomes i).2) threshold ≤ level0)
    (μ : Measure (ManuscriptOriginConfiguration n))
    (hstationary : μ.bind (fun c => c.refreshLaw) = μ)
    (hmarks : ∀ᵐ c ∂μ, c.MarksIn S)
    (pre : List (FixedLevelStep S)) (hpre : ∀ s ∈ pre, s ∈ full)
    (hcounts : μ.map (fun c : ManuscriptOriginConfiguration n =>
        c.source.pointCounts level0 S) =
      fixedLevelLaw pre
        (Measure.pi (fun _ : S => ProbabilityTheory.poissonMeasure 0))) :
    (μ.bind (manuscriptOriginGivenVolumesLaw hn prep b eta delta threshold
        components outcomes)) {c | level0 < c.level} ≤
      μ {c | level0 < c.level} + components.length * B := by
  induction components generalizing μ pre with
  | nil =>
      change (μ.bind Measure.dirac) _ ≤ _
      rw [Measure.bind_dirac]
      simp
  | cons d rest ih =>
      let intensity := ttcPseudocode.t b n threshold (outcomes 0).2
      let R := manuscriptOriginRefreshedComponentLaw hn d.polytope b eta
        threshold d.route intensity
      let G := manuscriptOriginGivenVolumesLaw hn prep b eta delta threshold
        rest (fun i => outcomes i.succ)
      have hR : Measurable R :=
        measurable_manuscriptOriginRefreshedComponentLaw hn d.polytope b eta
          threshold hthreshold d.route intensity
      have hG : Measurable G :=
        measurable_manuscriptOriginGivenVolumesLaw hn prep b eta delta
          threshold hthreshold rest (fun i => outcomes i.succ)
      have hbind : μ.bind (manuscriptOriginGivenVolumesLaw hn prep b eta delta
          threshold (d :: rest) outcomes) = (μ.bind R).bind G := by
        rw [Measure.bind_bind hR.aemeasurable hG.aemeasurable]
        rfl
      have hM : MeasurableSet
          {c : ManuscriptOriginConfiguration n | c.MarksIn S} :=
        measurableSet_manuscriptOriginMarksIn S
      have hsuppD := hsupport d List.mem_cons_self
      have hmarks' : ∀ᵐ c ∂(μ.bind R), c.MarksIn S := by
        apply ae_bind_of_ae_ae_marksIn hR.aemeasurable hM
        filter_upwards [hmarks] with c hc
        exact manuscriptOriginRefreshedComponentLaw_ae_marksIn hn d.polytope
          b eta threshold hthreshold d.route intensity S hsuppD c hc
      have hstat' : (μ.bind R).bind (fun c => c.refreshLaw) = μ.bind R :=
        manuscriptOriginRefreshedComponentLaw_bind_stationary hn d.polytope b
          eta threshold hthreshold d.route intensity μ
      let step : FixedLevelStep S :=
        (manuscriptOriginGivenVolumesSteps hn prep b eta delta threshold S
          level0 [d] (fun _ => outcomes 0)).head (by simp
            [manuscriptOriginGivenVolumesSteps])
      have hsingle : manuscriptOriginGivenVolumesSteps hn prep b eta delta
          threshold S level0 [d] (fun _ => outcomes 0) = [step] := by
        simp [step, manuscriptOriginGivenVolumesSteps]
      have hR1 : μ.bind (manuscriptOriginGivenVolumesLaw hn prep b eta delta
          threshold [d] (fun _ => outcomes 0)) = μ.bind R := by
        congr 1
        funext c
        change (R c).bind Measure.dirac = R c
        exact Measure.bind_dirac
      have hcounts' : (μ.bind R).map (fun c : ManuscriptOriginConfiguration n =>
          c.source.pointCounts level0 S) =
          fixedLevelLaw (pre ++ [step])
            (Measure.pi (fun _ : S => ProbabilityTheory.poissonMeasure 0)) := by
        have h := manuscriptOriginGivenVolumesLaw_fixedLevel hn prep b eta
          delta threshold hthreshold S level0 [d]
          (fun d' hd' => by
            rw [List.mem_singleton] at hd'
            subst hd'
            exact hsuppD)
          (fun _ => outcomes 0) μ hstationary
        rw [hR1, hsingle, hcounts] at h
        rw [h, fixedLevelLaw_append]
      have hstepMem : step ∈ full := by
        apply hsteps
        change step ∈ manuscriptOriginGivenVolumesSteps hn prep b eta delta
          threshold S level0 [d] (fun _ => outcomes 0) ++ _
        rw [hsingle]
        simp
      have hpre' : ∀ s ∈ pre ++ [step], s ∈ full := by
        intro s hs
        rcases List.mem_append.mp hs with hs | hs
        · exact hpre s hs
        · rw [List.mem_singleton] at hs
          subst hs
          exact hstepMem
      have hstepsRest : ∀ s ∈ manuscriptOriginGivenVolumesSteps hn prep b eta
          delta threshold S level0 rest (fun i => outcomes i.succ), s ∈ full := by
        intro s hs
        apply hsteps
        exact List.mem_cons_of_mem _ hs
      have hih := ih (fun d' hd' => hsupport d' (List.mem_cons_of_mem d hd'))
        (fun i => outcomes i.succ) hstepsRest (fun i c hc => hnocross i.succ c hc)
        (μ.bind R) hstat' hmarks' (pre ++ [step]) hpre' hcounts'
      have hone := manuscriptOrigin_refreshed_step_crossing hn d.polytope b eta
        threshold hthreshold d.route intensity S hsuppD level0
        (fun c hc => hnocross 0 c hc) μ hmarks
      have hcountMeas : Measurable (fun c : ManuscriptOriginConfiguration n =>
          c.source.pointCounts level0 S) :=
        (measurable_manuscriptOriginSourceState_pointCounts level0 S).comp
          measurable_manuscriptOriginConfiguration_source
      have hsumMeas : Measurable (fun v : S → Nat => ∑ x, v x) :=
        Measurable.of_discrete
      have hB : (μ.bind R)
          {c | threshold ≤ ((∑ x : S, c.source.pointCounts level0 S x : Nat) :
            Real)} ≤ B := by
        have hset : {c : ManuscriptOriginConfiguration n |
            threshold ≤ ((∑ x : S, c.source.pointCounts level0 S x : Nat) :
              Real)} =
            (fun c : ManuscriptOriginConfiguration n =>
              c.source.pointCounts level0 S) ⁻¹'
              ((fun v : S → Nat => ∑ x, v x) ⁻¹'
                {j : Nat | threshold ≤ (j : Real)}) := rfl
        rw [hset, ← Measure.map_apply hcountMeas
          (hsumMeas (MeasurableSet.of_discrete)), hcounts',
          ← Measure.map_apply hsumMeas (MeasurableSet.of_discrete)]
        exact hbudget _ hpre'
      rw [hbind]
      calc
        ((μ.bind R).bind G) {c | level0 < c.level} ≤
            (μ.bind R) {c | level0 < c.level} + rest.length * B := hih
        _ ≤ (μ {c | level0 < c.level} + B) + rest.length * B := by
          gcongr
          exact hone.trans (add_le_add_right hB _)
        _ = μ {c | level0 < c.level} + (d :: rest).length * B := by
          simp only [List.length_cons, Nat.cast_add, Nat.cast_one]
          ring

end Kr25Ssmxt

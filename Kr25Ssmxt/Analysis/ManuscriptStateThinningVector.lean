import Kr25Ssmxt.Analysis.ManuscriptStatePointCounts
import Kr25Ssmxt.Analysis.ManuscriptCoinBlockLaw
import Kr25Ssmxt.Analysis.ManuscriptBernoulliCount

/-! The whole point-count vector of stored copies after fixed-round thinning
is a function of independent Bernoulli decisions on their copy labels. -/

namespace Kr25Ssmxt

open Classical MeasureTheory

noncomputable def TTCState.pointCountsFromDecisions {n : Nat}
    (s : TTCState n) (S : Finset (LatticePoint n))
    (decisions : s.samples.image Prod.fst → Bool) : S → Nat :=
  fun x => (s.samples.filter fun copy =>
    copy.2 = x.1 ∧
      (if h : copy.1 ∈ s.samples.image Prod.fst then
        decisions ⟨copy.1, h⟩ else false) = true).card

theorem TTCState.pointCounts_samplesAfter_eq_decisions {n : Nat}
    (s : TTCState n) (S : Finset (LatticePoint n))
    (coins : Nat × Nat → Bool) (rounds : Nat) :
    ({s with samples := samplesAfter coins rounds s.samples}).pointCounts S =
      s.pointCountsFromDecisions S
        (fun label => labelSurvives rounds (fun r => coins (r, label.1))) := by
  funext x
  change ((samplesAfter coins rounds s.samples).filter
    fun copy => copy.2 = x.1).card =
    (s.samples.filter fun copy =>
      copy.2 = x.1 ∧
        (if h : copy.1 ∈ s.samples.image Prod.fst then
          labelSurvives rounds (fun r => coins (r, copy.1)) else false) = true).card
  congr 1
  ext copy
  by_cases hc : copy ∈ s.samples
  · have hl : copy.1 ∈ s.samples.image Prod.fst :=
      Finset.mem_image.mpr ⟨copy, hc, rfl⟩
    have hsurv :
        labelSurvives rounds (fun r => coins (r, copy.1)) = true ↔
          survives coins rounds copy.1 := by
      simp [labelSurvives, survives]
    simpa only [samplesAfter, Finset.mem_filter, hc, true_and, dif_pos hl, hsurv,
      and_comm] using (Iff.rfl :
        (copy.2 = x.1 ∧ survives coins rounds copy.1) ↔
          (copy.2 = x.1 ∧ survives coins rounds copy.1))
  · simp [samplesAfter, hc]

theorem TTCState.fixed_round_pointCounts_law {n : Nat}
    (s : TTCState n) (S : Finset (LatticePoint n))
    (rounds : Nat) :
    fairCoinStreamLaw.map (fun coins : Nat × Nat → Bool =>
      ({s with samples := samplesAfter coins rounds s.samples}).pointCounts S) =
    (Measure.pi (fun _ : s.samples.image Prod.fst =>
      ProbabilityTheory.bernoulliMeasure true false
        (survivalProbability rounds))).map
      (s.pointCountsFromDecisions S) := by
  let decisions : (Nat × Nat → Bool) →
      (s.samples.image Prod.fst → Bool) :=
    fun coins label => labelSurvives rounds (fun r => coins (r, label.1))
  have hdecisions : Measurable decisions := by
    exact measurable_pi_lambda _ (fun label =>
      (measurable_labelSurvives rounds).comp
        (measurable_pi_lambda _ (fun r => measurable_pi_apply (r, label.1))))
  have hcount : Measurable (s.pointCountsFromDecisions S) :=
    Measurable.of_discrete
  calc
    fairCoinStreamLaw.map (fun coins : Nat × Nat → Bool =>
        ({s with samples := samplesAfter coins rounds s.samples}).pointCounts S) =
      fairCoinStreamLaw.map
        (s.pointCountsFromDecisions S ∘ decisions) := by
          congr 1
          funext coins
          exact s.pointCounts_samplesAfter_eq_decisions S coins rounds
    _ = (fairCoinStreamLaw.map decisions).map
        (s.pointCountsFromDecisions S) := by
          rw [Measure.map_map hcount hdecisions]
    _ = _ := by
      rw [fairCoinStreamLaw_survivalVector_finite rounds
        (s.samples.image Prod.fst)]

/-- Stored point counts and the pending count use the same independent
label-indexed survival decisions.  This joint law is the fixed-round bridge
needed when the second manuscript loop tests their sum. -/
theorem TTCState.fixed_round_pointCounts_pending_law {n : Nat}
    (s : TTCState n) (S : Finset (LatticePoint n))
    (pending rounds : Nat) :
    fairCoinStreamLaw.map (fun coins : Nat × Nat → Bool =>
      (({s with samples := samplesAfter coins rounds s.samples}).pointCounts S,
        pendingAfter coins rounds s.nextLabel pending)) =
    (Measure.infinitePi (fun _ : Nat =>
      ProbabilityTheory.bernoulliMeasure true false
        (survivalProbability rounds))).map
      (fun decisions : Nat → Bool =>
        (s.pointCountsFromDecisions S
          (fun label => decisions label.1),
         ((Finset.range pending).filter
          (fun i => decisions (s.nextLabel + i) = true)).card)) := by
  let decisions : (Nat × Nat → Bool) → Nat → Bool :=
    fun coins label => labelSurvives rounds (fun r => coins (r, label))
  have hdecisions : Measurable decisions := by
    exact measurable_pi_lambda _ (fun label =>
      (measurable_labelSurvives rounds).comp
        (measurable_pi_lambda _ (fun r => measurable_pi_apply (r, label))))
  let output : (Nat → Bool) → (S → Nat) × Nat := fun bits =>
    (s.pointCountsFromDecisions S (fun label => bits label.1),
      ((Finset.range pending).filter
        (fun i => bits (s.nextLabel + i) = true)).card)
  have houtput : Measurable output := by
    have hstored : Measurable (fun bits : Nat → Bool =>
        s.pointCountsFromDecisions S (fun label => bits label.1)) := by
      have hrestrict : Measurable (fun bits : Nat → Bool =>
          fun label : s.samples.image Prod.fst => bits label.1) :=
        measurable_pi_lambda _ (fun label => measurable_pi_apply label.1)
      exact (Measurable.of_discrete :
        Measurable (s.pointCountsFromDecisions S)).comp hrestrict
    have hpending (T : Finset Nat) : Measurable (fun bits : Nat → Bool =>
        (T.filter (fun i => bits (s.nextLabel + i) = true)).card) := by
      induction T using Finset.induction_on with
      | empty => simpa using (measurable_const : Measurable (fun _ : Nat → Bool => (0 : Nat)))
      | @insert a T ha ih =>
          have heq : (fun bits : Nat → Bool =>
              ((insert a T).filter (fun i => bits (s.nextLabel + i) = true)).card) =
              fun bits => (if bits (s.nextLabel + a) = true then 1 else 0) +
                (T.filter (fun i => bits (s.nextLabel + i) = true)).card := by
            funext bits
            rw [Finset.filter_insert]
            by_cases hb : bits (s.nextLabel + a) = true
            · simp [hb, ha]; omega
            · simp [hb, ha]
          rw [heq]
          have hif : Measurable (fun bits : Nat → Bool =>
              if bits (s.nextLabel + a) = true then (1 : Nat) else 0) :=
            (Measurable.of_discrete : Measurable
              (fun b : Bool => if b = true then (1 : Nat) else 0)).comp
              (measurable_pi_apply (s.nextLabel + a))
          exact hif.add ih
    exact hstored.prodMk (hpending (Finset.range pending))
  have hpoint (coins : Nat × Nat → Bool) :
      (({s with samples := samplesAfter coins rounds s.samples}).pointCounts S,
        pendingAfter coins rounds s.nextLabel pending) =
      output (decisions coins) := by
    apply Prod.ext
    · exact s.pointCounts_samplesAfter_eq_decisions S coins rounds
    · simp only [output, decisions, pendingAfter]
      congr 1
      ext i
      simp only [Finset.mem_filter, Finset.mem_range]
      simp [labelSurvives, survives]
  calc
    fairCoinStreamLaw.map (fun coins : Nat × Nat → Bool =>
        (({s with samples := samplesAfter coins rounds s.samples}).pointCounts S,
          pendingAfter coins rounds s.nextLabel pending)) =
      fairCoinStreamLaw.map (output ∘ decisions) := by
        congr 1
        funext coins
        exact hpoint coins
    _ = (fairCoinStreamLaw.map decisions).map output := by
      rw [Measure.map_map houtput hdecisions]
    _ = _ := by
      rw [fairCoinStreamLaw_survivalVector rounds]
      simp only [labelStreamLaw_survivalProbability]
      rfl

/-- At each individual lattice point, the stored copies surviving a fixed
number of actual thinning rounds have the binomial law. -/
theorem TTCState.fixed_round_pointCount_binomial_law {n : Nat}
    (s : TTCState n) (x : LatticePoint n) (rounds : Nat)
    (h : s.LabelsFresh) :
    fairCoinStreamLaw.map (fun coins : Nat × Nat → Bool =>
      ({s with samples := samplesAfter coins rounds s.samples}).pointCount x) =
    ProbabilityTheory.binomial (s.pointCount x)
      (survivalProbability rounds) := by
  let restricted : TTCState n :=
    {s with samples := s.samples.filter (fun copy => copy.2 = x)}
  have hrestricted : restricted.LabelsFresh := by
    unfold TTCState.LabelsFresh at h ⊢
    constructor
    · intro copy hc
      exact h.1 copy (Finset.mem_filter.mp hc).1
    · intro copy hc other ho heq
      exact h.2 copy (Finset.mem_filter.mp hc).1
        other (Finset.mem_filter.mp ho).1 heq
  have hbin := restricted.fixed_round_population_binomial_law 0 rounds hrestricted
  have hpoint (coins : Nat × Nat → Bool) :
      ({s with samples := samplesAfter coins rounds s.samples}).pointCount x =
      (samplesAfter coins rounds restricted.samples).card := by
    change ((samplesAfter coins rounds s.samples).filter
      fun copy => copy.2 = x).card =
      (samplesAfter coins rounds (s.samples.filter
        fun copy => copy.2 = x)).card
    congr 1
    ext copy
    simp [samplesAfter, and_comm, and_left_comm]
  have hsize : restricted.samples.card = s.pointCount x := rfl
  calc
    fairCoinStreamLaw.map (fun coins : Nat × Nat → Bool =>
        ({s with samples := samplesAfter coins rounds s.samples}).pointCount x) =
      fairCoinStreamLaw.map (fun coins =>
        (samplesAfter coins rounds restricted.samples).card) := by
          congr 1
          funext coins
          exact hpoint coins
    _ = ProbabilityTheory.binomial (s.pointCount x)
          (survivalProbability rounds) := by
            simpa [restricted, TTCState.pointCount, pendingAfter] using hbin

end Kr25Ssmxt

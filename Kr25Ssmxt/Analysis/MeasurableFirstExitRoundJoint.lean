import Kr25Ssmxt.Analysis.MeasurableFirstExitRound

/-!
# Joint measurability of the first TTC thinning-exit round

The paper's samples are coded decimal-lattice points, hence the retained configuration and
the remaining loop-control data are countable.  After separating those controls from the
real-valued sampling rate, fixed-round exit events are jointly measurable by countable gluing.
-/

namespace Kr25Ssmxt

/--
For a fixed threshold, the first thinning-exit round is jointly measurable in the state,
pending count, and coin stream.

INTERNAL: countable-control measurability for the unbounded thinning loop.
-/
lemma measurable_firstExitRound_joint {n : Nat} (threshold : Real) :
    Measurable (fun z : (TTCState n × Nat) × (Nat × Nat → Bool) =>
      firstExitRound z.1.1 z.1.2 threshold z.2) := by
  let Control := (Finset (SampleCopy n) × Nat) × Nat
  let control : (TTCState n × Nat) × (Nat × Nat → Bool) →
      Control × (Nat × Nat → Bool) := fun z =>
    (((z.1.1.samples, z.1.1.nextLabel), z.1.2), z.2)
  have hstateCoords : Measurable
      (fun z : (TTCState n × Nat) × (Nat × Nat → Bool) =>
        (z.1.1.rate, z.1.1.samples, z.1.1.nextLabel)) :=
    (comap_measurable _).comp (measurable_fst.comp measurable_fst)
  have hsamples : Measurable
      (fun z : (TTCState n × Nat) × (Nat × Nat → Bool) => z.1.1.samples) :=
    (measurable_fst.comp measurable_snd).comp hstateCoords
  have hnext : Measurable
      (fun z : (TTCState n × Nat) × (Nat × Nat → Bool) => z.1.1.nextLabel) :=
    (measurable_snd.comp measurable_snd).comp hstateCoords
  have hpending : Measurable
      (fun z : (TTCState n × Nat) × (Nat × Nat → Bool) => z.1.2) :=
    measurable_snd.comp measurable_fst
  have hcoins : Measurable
      (fun z : (TTCState n × Nat) × (Nat × Nat → Bool) => z.2) :=
    measurable_snd
  have hcontrol : Measurable control :=
    ((hsamples.prodMk hnext).prodMk hpending).prodMk hcoins
  have hexit (rounds : Nat) : MeasurableSet
      {z : (TTCState n × Nat) × (Nat × Nat → Bool) |
        thinningExit z.1.1 z.1.2 threshold z.2 rounds} := by
    have hcontrolExit : Measurable (fun q : Control × (Nat × Nat → Bool) =>
        thinningExit
          ({ rate := 1, samples := q.1.1.1, nextLabel := q.1.1.2 } : TTCState n)
          q.1.2 threshold q.2 rounds) := by
      apply measurable_from_prod_countable_right
      intro c
      exact measurableSet_setOfPred.mp
        (measurableSet_thinningExit
          ({ rate := 1, samples := c.1.1, nextLabel := c.1.2 } : TTCState n)
          c.2 threshold rounds)
    exact (hcontrolExit.comp hcontrol).setOf
  apply measurable_to_countable'
  intro k
  cases k with
  | zero =>
      have hfiber :
          (fun z : (TTCState n × Nat) × (Nat × Nat → Bool) =>
            firstExitRound z.1.1 z.1.2 threshold z.2) ⁻¹' {0} =
            {z | thinningExit z.1.1 z.1.2 threshold z.2 0} ∪
              ⋂ r, {z | thinningExit z.1.1 z.1.2 threshold z.2 r}ᶜ := by
        ext z
        simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_union,
          Set.mem_ofPred_eq, Set.mem_iInter, Set.mem_compl_iff]
        rw [firstExitRound, Nat.sInf_eq_zero]
        constructor
        · rintro (h | h)
          · exact Or.inl h
          · exact Or.inr (fun r hr => (Set.eq_empty_iff_forall_notMem.mp h r) hr)
        · rintro (h | h)
          · exact Or.inl h
          · exact Or.inr (Set.eq_empty_iff_forall_notMem.mpr (fun r hr => h r hr))
      rw [hfiber]
      exact (hexit 0).union (MeasurableSet.iInter fun r => (hexit r).compl)
  | succ k =>
      have hfiber :
          (fun z : (TTCState n × Nat) × (Nat × Nat → Bool) =>
            firstExitRound z.1.1 z.1.2 threshold z.2) ⁻¹' {k + 1} =
            {z | thinningExit z.1.1 z.1.2 threshold z.2 (k + 1)} ∩
              {z | thinningExit z.1.1 z.1.2 threshold z.2 k}ᶜ := by
        ext z
        simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_inter_iff,
          Set.mem_ofPred_eq, Set.mem_compl_iff]
        have hup : ∀ r₁ r₂ : Nat, r₁ ≤ r₂ →
            r₁ ∈ {r | thinningExit z.1.1 z.1.2 threshold z.2 r} →
            r₂ ∈ {r | thinningExit z.1.1 z.1.2 threshold z.2 r} := by
          intro r₁ r₂ hr h
          exact thinningExit_mono_rounds z.1.1 z.1.2 threshold z.2 hr h
        exact Nat.sInf_upward_closed_eq_succ_iff hup k
      rw [hfiber]
      exact (hexit (k + 1)).inter (hexit k).compl

end Kr25Ssmxt

/-! ### Run record
Newest first. History, not instruction — what this file claims is above.

* this round · proved · coded paper lattice points make the finite control state countable
* previous round · diagnosed · arbitrary real-valued sample states made sample emptiness nonmeasurable
-/

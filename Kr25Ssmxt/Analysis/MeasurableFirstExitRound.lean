import Kr25Ssmxt.Analysis.MeasurableSetThinningExit
import Kr25Ssmxt.Analysis.ThinningExitMonoRounds

/-!
# Measurability of the first thinning-exit round

The zero fiber includes both immediate exit and the exceptional case in which no round
exits. Successor fibers are the difference between two consecutive upward-closed exit
events.
-/

namespace Kr25Ssmxt

/--
The least thinning-exit round, with `sInf ∅ = 0`, is measurable in the coin stream.

INTERNAL: Measurability of the only unbounded control-flow choice in thinning.
-/
lemma measurable_firstExitRound {n : Nat} (s : TTCState n) (pending : Nat)
    (threshold : Real) : Measurable (ttcPseudocode.secondLoopExitRound s pending threshold) := by
  apply measurable_to_countable'
  intro k
  cases k with
  | zero =>
      have hfiber :
          (ttcPseudocode.secondLoopExitRound s pending threshold) ⁻¹' {0} =
            {coins : Nat × Nat → Bool |
              ttcPseudocode.secondLoopExit s pending threshold coins 0} ∪
            ⋂ r, {coins : Nat × Nat → Bool |
              ttcPseudocode.secondLoopExit s pending threshold coins r}ᶜ := by
        ext coins
        simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_union,
          Set.mem_setOf_eq, Set.mem_iInter, Set.mem_compl_iff]
        rw [ttcPseudocode.secondLoopExitRound, Nat.sInf_eq_zero]
        constructor
        · rintro (hexit | hempty)
          · exact Or.inl hexit
          · right
            intro r hr
            exact (Set.eq_empty_iff_forall_notMem.mp hempty r) hr
        · rintro (hexit | hnever)
          · exact Or.inl hexit
          · right
            apply Set.eq_empty_iff_forall_notMem.mpr
            intro r hr
            exact hnever r hr
      rw [hfiber]
      exact (measurableSet_thinningExit s pending threshold 0).union
        (MeasurableSet.iInter fun r =>
          (measurableSet_thinningExit s pending threshold r).compl)
  | succ k =>
      have hfiber :
          (ttcPseudocode.secondLoopExitRound s pending threshold) ⁻¹' {k + 1} =
            {coins : Nat × Nat → Bool |
              ttcPseudocode.secondLoopExit s pending threshold coins (k + 1)} ∩
            {coins : Nat × Nat → Bool |
              ttcPseudocode.secondLoopExit s pending threshold coins k}ᶜ := by
        ext coins
        simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_inter_iff,
          Set.mem_setOf_eq, Set.mem_compl_iff]
        have hup : ∀ r₁ r₂ : Nat, r₁ ≤ r₂ →
            r₁ ∈ {r | ttcPseudocode.secondLoopExit s pending threshold coins r} →
            r₂ ∈ {r | ttcPseudocode.secondLoopExit s pending threshold coins r} := by
          intro r₁ r₂ hr hexit
          exact thinningExit_mono_rounds s pending threshold coins hr hexit
        exact Nat.sInf_upward_closed_eq_succ_iff hup k
      rw [hfiber]
      exact (measurableSet_thinningExit s pending threshold (k + 1)).inter
        (measurableSet_thinningExit s pending threshold k).compl

end Kr25Ssmxt

/-! ### Run record
Newest first. History, not instruction — what this file claims is above.

* r1 · proved · exposed zero and successor fibers of the upward-closed exit-round set
-/

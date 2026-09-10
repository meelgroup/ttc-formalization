import Kr25Ssmxt.Model.Prelude

/-!
# Measurability of finite survival events

Survival through a fixed number of thinning rounds depends on finitely many Boolean
coordinates of the coin stream.
-/

namespace Kr25Ssmxt

/--
The event that one labelled copy survives a fixed number of rounds is measurable.

INTERNAL: Cylinder-event measurability for the coupled thinning construction.
-/
lemma measurableSet_survives (rounds label : Nat) :
    MeasurableSet {coins : Nat × Nat → Bool | survives coins rounds label} := by
  induction rounds with
  | zero =>
      simp [survives]
  | succ rounds ih =>
      have hset :
          {coins : Nat × Nat → Bool | survives coins (rounds + 1) label} =
            {coins | survives coins rounds label} ∩
              {coins | coins (rounds, label) = true} := by
        ext coins
        simp only [Set.mem_setOf_eq, Set.mem_inter_iff]
        constructor
        · intro h
          exact ⟨fun r hr => h r (Nat.lt_succ_of_lt hr), h rounds (Nat.lt_succ_self rounds)⟩
        · rintro ⟨hprev, hlast⟩ r hr
          have hle : r ≤ rounds := Nat.lt_succ_iff.mp (by simpa using hr)
          rcases lt_or_eq_of_le hle with hlt | rfl
          · exact hprev r hlt
          · exact hlast
      rw [hset]
      apply ih.inter
      change MeasurableSet ((fun coins : Nat × Nat → Bool => coins (rounds, label)) ⁻¹' {true})
      exact (measurable_pi_apply (rounds, label)) (measurableSet_singleton true)

end Kr25Ssmxt

/-! ### Run record
Newest first. History, not instruction — what this file claims is above.

* r1 · proved · decomposed successor survival into the prior event and one Boolean cylinder
-/

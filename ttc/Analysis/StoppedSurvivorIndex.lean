import ttc.Analysis.SurvivorRelabel

/-! Survivor indices and selected original labels depend only on the
stopped coin prefix. -/

namespace ttc

theorem pendingSurvivorIndices_coinPrefix
    (coins : Nat × Nat → Bool) (rounds firstLabel pending : Nat) :
    pendingSurvivorIndices (coinPrefix rounds coins) rounds firstLabel
      pending =
    pendingSurvivorIndices coins rounds firstLabel pending := by
  classical
  ext i
  simp only [pendingSurvivorIndices, Finset.mem_filter,
    Finset.mem_range]
  exact and_congr Iff.rfl
    (survives_coinPrefix_iff rounds rounds (firstLabel + i)
      (le_refl rounds) coins)

theorem pendingSurvivorIndices_eq_of_prefix_eq
    (coins coins' : Nat × Nat → Bool) (rounds firstLabel pending : Nat)
    (hprefix : coinPrefix rounds coins = coinPrefix rounds coins') :
    pendingSurvivorIndices coins rounds firstLabel pending =
    pendingSurvivorIndices coins' rounds firstLabel pending := by
  calc
    pendingSurvivorIndices coins rounds firstLabel pending =
      pendingSurvivorIndices (coinPrefix rounds coins) rounds firstLabel
        pending := (pendingSurvivorIndices_coinPrefix coins rounds
          firstLabel pending).symm
    _ = pendingSurvivorIndices (coinPrefix rounds coins') rounds firstLabel
        pending := by rw [hprefix]
    _ = pendingSurvivorIndices coins' rounds firstLabel pending :=
      pendingSurvivorIndices_coinPrefix coins' rounds firstLabel pending

theorem pendingSurvivorFin_eq_of_prefix_eq
    (coins coins' : Nat × Nat → Bool) (rounds firstLabel pending : Nat)
    (hprefix : coinPrefix rounds coins = coinPrefix rounds coins')
    (i : Fin (pendingAfter coins rounds firstLabel pending)) :
    (pendingSurvivorFin coins rounds firstLabel pending i).val =
      (pendingSurvivorFin coins' rounds firstLabel pending
        ⟨i.val, by
          have hcount : pendingAfter coins rounds firstLabel pending =
              pendingAfter coins' rounds firstLabel pending := by
            calc
              _ = pendingAfter (coinPrefix rounds coins) rounds
                firstLabel pending :=
                  (pendingAfter_coinPrefix rounds rounds firstLabel pending
                    (le_refl rounds) coins).symm
              _ = pendingAfter (coinPrefix rounds coins') rounds
                firstLabel pending := by rw [hprefix]
              _ = _ := pendingAfter_coinPrefix rounds rounds firstLabel
                pending (le_refl rounds) coins'
          omega⟩).val := by
  classical
  have hindices := pendingSurvivorIndices_eq_of_prefix_eq
    coins coins' rounds firstLabel pending hprefix
  unfold pendingSurvivorFin
  simp only [hindices, Finset.orderEmbOfFin_eq_orderEmbOfFin_iff]

theorem twoStageSurvivorLabel_eq_of_active_prefix_eq
    (preCoins : Nat × Nat → Bool)
    (preRounds firstLabel basePending : Nat)
    (active active' : Nat × Fin
      (pendingAfter preCoins preRounds firstLabel basePending) → Bool)
    (rounds : Nat)
    (hprefix : coinPrefix rounds
        (pendingCoinExtension firstLabel
          (pendingAfter preCoins preRounds firstLabel basePending)
          active) =
      coinPrefix rounds
        (pendingCoinExtension firstLabel
          (pendingAfter preCoins preRounds firstLabel basePending)
          active'))
    (i : Fin (pendingAfter
      (pendingCoinExtension firstLabel
        (pendingAfter preCoins preRounds firstLabel basePending) active)
      rounds firstLabel
      (pendingAfter preCoins preRounds firstLabel basePending))) :
    twoStageSurvivorLabel preCoins preRounds firstLabel basePending
      active rounds i =
    twoStageSurvivorLabel preCoins preRounds firstLabel basePending
      active' rounds
      ⟨i.val, by
        have hcount : pendingAfter
            (pendingCoinExtension firstLabel
              (pendingAfter preCoins preRounds firstLabel basePending)
              active) rounds firstLabel
              (pendingAfter preCoins preRounds firstLabel basePending) =
            pendingAfter
              (pendingCoinExtension firstLabel
                (pendingAfter preCoins preRounds firstLabel basePending)
                active') rounds firstLabel
                (pendingAfter preCoins preRounds firstLabel basePending) := by
          calc
            _ = pendingAfter (coinPrefix rounds
                (pendingCoinExtension firstLabel
                  (pendingAfter preCoins preRounds firstLabel basePending)
                  active)) rounds firstLabel _ :=
                    (pendingAfter_coinPrefix rounds rounds firstLabel _
                      (le_refl rounds) _).symm
            _ = pendingAfter (coinPrefix rounds
                (pendingCoinExtension firstLabel
                  (pendingAfter preCoins preRounds firstLabel basePending)
                  active')) rounds firstLabel _ := by rw [hprefix]
            _ = _ := pendingAfter_coinPrefix rounds rounds firstLabel _
              (le_refl rounds) _
        omega⟩ := by
  have hfin := pendingSurvivorFin_eq_of_prefix_eq
    (pendingCoinExtension firstLabel
      (pendingAfter preCoins preRounds firstLabel basePending) active)
    (pendingCoinExtension firstLabel
      (pendingAfter preCoins preRounds firstLabel basePending) active')
    rounds firstLabel
    (pendingAfter preCoins preRounds firstLabel basePending) hprefix i
  simp only [twoStageSurvivorLabel]
  exact congrArg
    (fun j : Fin (pendingAfter preCoins preRounds firstLabel basePending) =>
      firstLabel +
        (pendingSurvivorFin preCoins preRounds firstLabel basePending j).val)
    (Fin.ext hfin)

theorem originalSurvivorExtension_prefix_eq_of_jointPrefix_eq
    (preCoins : Nat × Nat → Bool)
    (preRounds firstLabel basePending rounds : Nat)
    (coins coins' : Nat × Nat → Bool)
    (hprefix : coinPrefix rounds coins = coinPrefix rounds coins') :
    coinPrefix rounds
      (pendingCoinExtension firstLabel
        (pendingAfter preCoins preRounds firstLabel basePending)
        (originalSurvivorCoinRestriction preCoins preRounds firstLabel
          basePending (jointFreshRead coins))) =
    coinPrefix rounds
      (pendingCoinExtension firstLabel
        (pendingAfter preCoins preRounds firstLabel basePending)
        (originalSurvivorCoinRestriction preCoins preRounds firstLabel
          basePending (jointFreshRead coins'))) := by
  funext pair
  by_cases hr : pair.1 < rounds
  · have hfresh (label : Nat) :
        jointFreshRead coins (pair.1, label) =
        jointFreshRead coins' (pair.1, label) := by
      calc
        jointFreshRead coins (pair.1, label) =
          jointFreshRead (coinPrefix rounds coins)
            (pair.1, label) :=
              (jointFreshRead_prefix coins rounds
                (pair.1, label) hr).symm
        _ = jointFreshRead (coinPrefix rounds coins')
            (pair.1, label) := by rw [hprefix]
        _ = jointFreshRead coins' (pair.1, label) :=
          jointFreshRead_prefix coins' rounds
            (pair.1, label) hr
    by_cases hlabel : firstLabel ≤ pair.2 ∧
        pair.2 < firstLabel +
          pendingAfter preCoins preRounds firstLabel basePending
    · simp only [coinPrefix, hr, ite_true, pendingCoinExtension,
        hlabel, dite_true, originalSurvivorCoinRestriction]
      exact hfresh _
    · simp [coinPrefix, hr, pendingCoinExtension, hlabel]
  · simp [coinPrefix, hr]

end ttc

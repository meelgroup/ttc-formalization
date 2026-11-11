import Kr25Ssmxt.Analysis.OriginAppendMeasurable

/-! A total, measurable selector for the increasing enumeration of surviving
pending labels. The zero value outside the surviving range is immaterial to
the origin append, which reads only valid indices. -/

namespace Kr25Ssmxt

open MeasureTheory

noncomputable def pendingSurvivorIndexOrZero
    (coins : Nat × Nat → Bool) (rounds firstLabel pending i : Nat) : Nat :=
  if h : i < pendingAfter coins rounds firstLabel pending then
    (pendingSurvivorFin coins rounds firstLabel pending ⟨i, h⟩).val
  else 0

theorem pendingSurvivorIndexOrZero_of_lt
    (coins : Nat × Nat → Bool) (rounds firstLabel pending i : Nat)
    (h : i < pendingAfter coins rounds firstLabel pending) :
    pendingSurvivorIndexOrZero coins rounds firstLabel pending i =
      (pendingSurvivorFin coins rounds firstLabel pending ⟨i, h⟩).val := by
  simp [pendingSurvivorIndexOrZero, h]

theorem measurable_pendingSurvivorIndexOrZero_fixed
    (rounds firstLabel pending i : Nat) :
    Measurable (fun coins : Nat × Nat → Bool =>
      pendingSurvivorIndexOrZero coins rounds firstLabel pending i) := by
  let select : Finset Nat → Nat := fun T =>
    if h : i < T.card then T.orderEmbOfFin rfl ⟨i, h⟩ else 0
  have hselect : Measurable select := measurable_of_countable _
  have hsets := measurable_pendingSurvivorIndices_fixed
    rounds firstLabel pending
  have heq : (fun coins : Nat × Nat → Bool =>
      pendingSurvivorIndexOrZero coins rounds firstLabel pending i) =
      (fun coins => select (pendingSurvivorIndices coins rounds
        firstLabel pending)) := by
    funext coins
    by_cases h : i < pendingAfter coins rounds firstLabel pending
    · simp [pendingSurvivorIndexOrZero, select, h,
        pendingSurvivorFin, pendingSurvivorIndices_card]
    · simp [pendingSurvivorIndexOrZero, select, h,
        pendingSurvivorIndices_card]
  rw [heq]
  exact hselect.comp hsets

theorem measurable_pendingSurvivorIndexOrZero_joint :
    Measurable (fun z : (Nat × Nat × Nat × Nat) ×
        (Nat × Nat → Bool) =>
      pendingSurvivorIndexOrZero z.2 z.1.1 z.1.2.1
        z.1.2.2.1 z.1.2.2.2) := by
  apply measurable_from_prod_countable_right
  intro params
  exact measurable_pendingSurvivorIndexOrZero_fixed
    params.1 params.2.1 params.2.2.1 params.2.2.2

theorem measurable_pendingAfter_joint :
    Measurable (fun z : (Nat × Nat × Nat) × (Nat × Nat → Bool) =>
      pendingAfter z.2 z.1.1 z.1.2.1 z.1.2.2) := by
  apply measurable_from_prod_countable_right
  intro params
  exact measurable_pendingAfter_fixed params.1 params.2.1 params.2.2

noncomputable def twoStageSurvivorLabelOrZero
    (preCoins activeCoins : Nat × Nat → Bool)
    (preRounds firstLabel basePending activeRounds i : Nat) : Nat :=
  firstLabel + pendingSurvivorIndexOrZero preCoins preRounds firstLabel
    basePending (pendingSurvivorIndexOrZero activeCoins activeRounds
      firstLabel (pendingAfter preCoins preRounds firstLabel basePending) i)

theorem measurable_twoStageSurvivorLabelOrZero_fixed
    (preRounds firstLabel basePending activeRounds i : Nat) :
    Measurable (fun coins : (Nat × Nat → Bool) × (Nat × Nat → Bool) =>
      twoStageSurvivorLabelOrZero coins.1 coins.2 preRounds firstLabel
        basePending activeRounds i) := by
  have hcount : Measurable (fun coins :
      (Nat × Nat → Bool) × (Nat × Nat → Bool) =>
      pendingAfter coins.1 preRounds firstLabel basePending) :=
    (measurable_pendingAfter_fixed preRounds firstLabel basePending).comp
      measurable_fst
  have hactive : Measurable (fun coins :
      (Nat × Nat → Bool) × (Nat × Nat → Bool) =>
      pendingSurvivorIndexOrZero coins.2 activeRounds firstLabel
        (pendingAfter coins.1 preRounds firstLabel basePending) i) :=
    measurable_pendingSurvivorIndexOrZero_joint.comp
      ((measurable_const.prodMk
        (measurable_const.prodMk (hcount.prodMk measurable_const))).prodMk
          measurable_snd)
  have hpre : Measurable (fun coins :
      (Nat × Nat → Bool) × (Nat × Nat → Bool) =>
      pendingSurvivorIndexOrZero coins.1 preRounds firstLabel
        basePending
        (pendingSurvivorIndexOrZero coins.2 activeRounds firstLabel
          (pendingAfter coins.1 preRounds firstLabel basePending) i)) :=
    measurable_pendingSurvivorIndexOrZero_joint.comp
      ((measurable_const.prodMk
        (measurable_const.prodMk
          (measurable_const.prodMk hactive))).prodMk measurable_fst)
  exact (measurable_const.add hpre)

theorem measurable_twoStageSurvivorLabelOrZero_joint :
    Measurable (fun z : (Nat × Nat × Nat × Nat × Nat) ×
        ((Nat × Nat → Bool) × (Nat × Nat → Bool)) =>
      twoStageSurvivorLabelOrZero z.2.1 z.2.2 z.1.1 z.1.2.1
        z.1.2.2.1 z.1.2.2.2.1 z.1.2.2.2.2) := by
  apply measurable_from_prod_countable_right
  intro params
  exact measurable_twoStageSurvivorLabelOrZero_fixed
    params.1 params.2.1 params.2.2.1 params.2.2.2.1 params.2.2.2.2

theorem twoStageSurvivorLabelOrZero_eq
    (preCoins : Nat × Nat → Bool)
    (preRounds firstLabel basePending activeRounds : Nat)
    (activeCoins : Nat × Fin
      (pendingAfter preCoins preRounds firstLabel basePending) → Bool)
    (i : Fin (pendingAfter
      (pendingCoinExtension firstLabel
        (pendingAfter preCoins preRounds firstLabel basePending)
        activeCoins)
      activeRounds firstLabel
      (pendingAfter preCoins preRounds firstLabel basePending))) :
    twoStageSurvivorLabelOrZero preCoins
      (pendingCoinExtension firstLabel
        (pendingAfter preCoins preRounds firstLabel basePending)
        activeCoins)
      preRounds firstLabel basePending activeRounds i.val =
    twoStageSurvivorLabel preCoins preRounds firstLabel basePending
      activeCoins activeRounds i := by
  let pending := pendingAfter preCoins preRounds firstLabel basePending
  let fresh := pendingCoinExtension firstLabel pending activeCoins
  let j := pendingSurvivorFin fresh activeRounds firstLabel pending i
  change firstLabel + pendingSurvivorIndexOrZero preCoins preRounds
      firstLabel basePending
      (pendingSurvivorIndexOrZero fresh activeRounds firstLabel pending
        i.val) =
    firstLabel + (pendingSurvivorFin preCoins preRounds firstLabel
      basePending j).val
  rw [pendingSurvivorIndexOrZero_of_lt fresh activeRounds firstLabel
    pending i.val i.isLt]
  exact congrArg (fun k => firstLabel + k)
    (pendingSurvivorIndexOrZero_of_lt preCoins preRounds firstLabel
      basePending j.val j.isLt)

/-- The finite-label fresh coin array used by the second loop, extended to
all labels, varies measurably with its two integer controls. -/
theorem measurable_originalSurvivorCoinExtension_parameters
    (preCoins future : Nat × Nat → Bool) (basePending : Nat) :
    Measurable (fun params : Nat × Nat =>
      pendingCoinExtension params.2
        (pendingAfter preCoins params.1 params.2 basePending)
        (originalSurvivorCoinRestriction preCoins params.1 params.2
          basePending future)) :=
  measurable_of_countable _

end Kr25Ssmxt

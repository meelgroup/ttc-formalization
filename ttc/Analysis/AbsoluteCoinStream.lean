import ttc.Analysis.ComponentPredrawTape
import Mathlib.Probability.Independence.InfinitePi

/-! Fresh relative thinning rounds can be read from any absolute dyadic level
of an independent fair-coin array without changing their joint law. -/

namespace ttc

open MeasureTheory

def shiftCoins (offset : Nat) (coins : Nat × Nat → Bool) : Nat × Nat → Bool :=
  fun pair => coins (pair.1 + offset, pair.2)

theorem shiftCoins_injective_index (offset : Nat) :
    Function.Injective (fun pair : Nat × Nat => (pair.1 + offset, pair.2)) := by
  intro a b h
  exact Prod.ext (Nat.add_right_cancel (congrArg Prod.fst h))
    (by simpa using congrArg Prod.snd h)

theorem fairCoinStreamLaw_shift (offset : Nat) :
    fairCoinStreamLaw.map (shiftCoins offset) = fairCoinStreamLaw := by
  letI : IsProbabilityMeasure fairCoinLaw := fairCoinLaw_isProbabilityMeasure
  letI : ∀ i : Nat × Nat,
      IsProbabilityMeasure ((fun _ : Nat × Nat => fairCoinLaw) i) :=
    fun _ => inferInstance
  change (Measure.infinitePi (fun _ : Nat × Nat => fairCoinLaw)).map
      (fun coins pair => coins (pair.1 + offset, pair.2)) =
    Measure.infinitePi (fun _ : Nat × Nat => fairCoinLaw)
  exact Measure.map_infinitePi_infinitePi_of_inj
    (P := fun _ : Nat × Nat => fairCoinLaw)
    (shiftCoins_injective_index offset)

end ttc

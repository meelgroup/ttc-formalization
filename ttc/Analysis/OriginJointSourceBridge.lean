import ttc.Analysis.SurvivorRelabel
import ttc.Analysis.OriginUnusedTailStep

/-! Pathwise bridge from the refreshed ghost source to the joint fair
source used by the survivor-filtered stopping theorem. -/

namespace ttc

theorem OriginConfiguration.refreshFuture_shift_oldCoins
    {n : Nat} (c : OriginConfiguration n)
    (oldFuture : Nat × (Nat × Nat) → Bool) (rounds : Nat) :
    shiftCoins rounds
      (sourceOldCoins c.origin
        (c.refreshFuture oldFuture).source.coins c.level) =
    (fun pair => oldFuture
      ((c.origin pair.2).1,
        (rounds + pair.1, (c.origin pair.2).2))) := by
  have hbase : sourceOldCoins c.origin
      (c.refreshFuture oldFuture).source.coins c.level =
      (fun pair => oldFuture
        ((c.origin pair.2).1, (pair.1, (c.origin pair.2).2))) :=
    c.refreshFuture_oldCoins oldFuture
  rw [hbase]
  funext pair
  simp [shiftCoins, Nat.add_comm]

end ttc

import Kr25Ssmxt.Analysis.ManuscriptSurvivorRelabel
import Kr25Ssmxt.Analysis.ManuscriptOriginUnusedTailStep

/-! Pathwise bridge from the refreshed ghost source to the joint fair
source used by the survivor-filtered stopping theorem. -/

namespace Kr25Ssmxt

theorem ManuscriptOriginConfiguration.refreshFuture_shift_oldCoins
    {n : Nat} (c : ManuscriptOriginConfiguration n)
    (oldFuture : Nat × (Nat × Nat) → Bool) (rounds : Nat) :
    shiftCoins rounds
      (manuscriptSourceOldCoins c.origin
        (c.refreshFuture oldFuture).source.coins c.level) =
    (fun pair => oldFuture
      ((c.origin pair.2).1,
        (rounds + pair.1, (c.origin pair.2).2))) := by
  have hbase : manuscriptSourceOldCoins c.origin
      (c.refreshFuture oldFuture).source.coins c.level =
      (fun pair => oldFuture
        ((c.origin pair.2).1, (pair.1, (c.origin pair.2).2))) :=
    c.refreshFuture_oldCoins oldFuture
  rw [hbase]
  funext pair
  simp [shiftCoins, Nat.add_comm]

end Kr25Ssmxt

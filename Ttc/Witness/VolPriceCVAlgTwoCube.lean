/-
Copyright (c) 2026 Uddalok Sarkar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Uddalok Sarkar
-/
import Ttc.Exec.VolPriceCVAlg
import Ttc.Witness.FullTwoCube

/-!
# Non-vacuity of the Cousins–Vempala volume price, at the two-cube witness

Split out of `Ttc/Exec/VolPriceCVAlg.lean`.  These are `CLAUDE.md` §11 witnesses — they show
the seven hypotheses of `Ttc.ttcVolPriceCVAlg_le` are jointly satisfiable — and a witness
belongs *downstream* of what it witnesses.  Keeping them in `VolPriceCVAlg` put
`Ttc/Witness/FullTwoCube.lean`, and through it `Ttc/Model/Theorem.lean`, in the import closure
of every capstone built over that file, which made it impossible to state a runtime theorem
about the constructed oracle inside `Ttc/Model/Theorem.lean` without a cycle.

Nothing about the statements changed in the move.
-/

namespace Ttc

open MeasureTheory Metric Set

variable {A : Type*} {n : ℕ}

/-! ## §8  Non-vacuity

The seven hypotheses of `Ttc.ttcVolPriceCVAlg_le` are conditions on `(atoms, φ, ε, δ, n)`,
so the bound would be vacuous if no input met them.  `Ttc/Witness/FullTwoCube.lean`'s
two-cube data meets them at **every** `n ≥ 1` and **every** `(ε, δ) ∈ (0,1]²` — it is the
same witness `Ttc.ttc_volume_estimate_two_cube_full` uses — and there the price is a
*positive* natural, so neither the bound nor the positivity statement is empty. -/

/-- **Non-vacuity: the whole bundle is inhabited, and the price is positive there.**

At the two-cube witness (`Ttc.TwoCube.atomsT`, `Ttc.TwoCube.twoForm`), at every `n ≥ 1` and
every `(ε, δ) ∈ (0,1]²`: `hφ` is `Ttc.TwoCube.twoForm_isPositive` and `hpos` is
`Ttc.TwoCube.twoVolPos`, so all seven hypotheses of `Ttc.ttcVolPriceCVAlg_le` hold
simultaneously, and `0 < ttcVolPriceCVAlg …` — the price is not the trivial `0`. -/
theorem ttcVolPriceCVAlg_pos_two_cube (m : ℕ) (hm : 1 ≤ m) (a b : ℝ) (ha0 : 0 < a)
    (ha1 : a ≤ 1) (_hb0 : 0 < b) (_hb1 : b ≤ 1) :
    0 < ttcVolPriceCVAlg (TwoCube.atomsT m hm a b ha0 ha1) (TwoCube.twoForm m) a b :=
  ttcVolPriceCVAlg_pos (TwoCube.atomsT m hm a b ha0 ha1) (TwoCube.twoForm m) a b ha0 ha1 hm
    TwoCube.twoForm_isPositive (TwoCube.twoVolPos m hm a b ha0 ha1)

/-- **The bound itself, at the same witness** — so that `Ttc.ttcVolPriceCVAlg_le` is known to
have at least one instance whose hypotheses are all met. -/
theorem ttcVolPriceCVAlg_le_two_cube (m : ℕ) (hm : 1 ≤ m) (a b : ℝ) (ha0 : 0 < a)
    (ha1 : a ≤ 1) (hb0 : 0 < b) (hb1 : b ≤ 1) :
    (ttcVolPriceCVAlg (TwoCube.atomsT m hm a b ha0 ha1) (TwoCube.twoForm m) a b : ℝ)
      ≤ 2 ^ 42 * (m : ℝ) ^ 4
          * ((canonRfac (toDNFd (preprocess (TwoCube.atomsT m hm a b ha0 ha1)
                (TwoCube.twoForm m))) + 1)
              * Real.log (8 / (algBlock (TwoCube.atomsT m hm a b ha0 ha1)
                  (TwoCube.twoForm m) a b).epsPrime ^ 2)
              * (cvAlgL (TwoCube.atomsT m hm a b ha0 ha1) (TwoCube.twoForm m) a b ^ 4
                  * Real.log (1 / (algBlock (TwoCube.atomsT m hm a b ha0 ha1)
                      (TwoCube.twoForm m) a b).deltaPrime)
                  / cvAlgKappa (TwoCube.atomsT m hm a b ha0 ha1)
                      (TwoCube.twoForm m) a b ^ 3)) :=
  ttcVolPriceCVAlg_le (TwoCube.atomsT m hm a b ha0 ha1) (TwoCube.twoForm m) a b ha0 ha1 hm
    TwoCube.twoForm_isPositive (TwoCube.twoVolPos m hm a b ha0 ha1) hb0 hb1

end Ttc

#print axioms Ttc.ttcVolPriceCVAlg_pos_two_cube
#print axioms Ttc.ttcVolPriceCVAlg_le_two_cube

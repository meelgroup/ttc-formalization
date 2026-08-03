/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import Ttc.Analysis.Capstone
import Ttc.Analysis.NumLatticeModel
import Ttc.Analysis.SketchProcess

/-!
# `lem:numlattice`, derived

`Ttc.TtcProb` does not assume `lem:numlattice`, and no longer assumes the epoch
covering either: the covering is itself a theorem
(`Ttc.TtcProb.numlattice_union`, `Analysis/NumLatticeModel`), proved from the
structure's description of the sampler. Everything quantitative is proved here:

* each `Err(j)` costs `2exp(−ε'²·λⱼ/3)` (`Ttc.levelLaw_err_le`, from the Poisson
  tail bound `Ttc.poisson_relative`);
* each overflow costs `exp(−Thresh/6)` (`Ttc.levelLaw_noise_le`);
* the epochs sum to `4exp(−a)` (`Ttc.err_branch_sum`);
* and the three contributions total at most `δ` at the algorithm's own `Thresh`
  and `δ'` (`Ttc.numlattice_failure_le`).

So this file is where the *covering* is turned into the paper's conclusion, using
the algorithm's constants and nothing else.

README finding 15 — that the paper's `Err(j)` is about a level-`j` process it
never couples to the run — is **repaired**: the coupling is constructed in
`Analysis/Coupling` and identified with the run in `Analysis/RunCoupling`. What
remains assumed is that the implementation's sampler *is* that family
(`Ttc.TtcProb.law_eq`, `oracle_eq`). See `AUDIT.md` §4.
-/

namespace Ttc

open MeasureTheory

namespace TtcProb

variable {A : Type*} {n : ℕ} (T : TtcProb A n)

/-- `ε' = ε/12` lies strictly inside `(0,1)`. -/
theorem epsPrime_lt_one : T.P.epsPrime < 1 := by
  have h := T.P.hε1
  rw [Params.epsPrime]
  linarith

/-- **`lem:numlattice`, as a theorem.**

With probability at least `1 − δ` the algorithm's output lies within `(1 ± ε/3)`
of the normalised lattice count. Formerly a field of `Ttc.TtcProb`; now derived
from the epoch decomposition plus the proved estimates. -/
theorem numlattice :
    1 - T.δ ≤
      (T.μ {ω | (1 - T.ε / 3) * T.L ≤ ttcOutput T.P T.O T.fuel T.ρ T.D ω ∧
                ttcOutput T.P T.O T.fuel T.ρ T.D ω ≤ (1 + T.ε / 3) * T.L}).toReal := by
  haveI := T.mΩ
  haveI := T.isProb
  obtain ⟨jstar, lamStar, hlam, hcover⟩ := T.numlattice_union
  set good : Set T.Ω := {ω | (1 - T.ε / 3) * T.L ≤ ttcOutput T.P T.O T.fuel T.ρ T.D ω ∧
    ttcOutput T.P T.O T.fuel T.ρ T.D ω ≤ (1 + T.ε / 3) * T.L} with hgood
  -- the three contributions total at most `δ`
  have hm : (1:ℝ) ≤ (T.P.m : ℝ) := by exact_mod_cast T.P.hm
  have hδ0 : 0 < T.δ := T.hδ0
  have hδP : T.P.δ = T.δ := T.delta_eq
  have hT1 : 24 * Real.log (24 / T.δ) / ((1 - T.P.epsPrime) * T.P.epsPrime ^ 2)
      ≤ T.P.thresh := by
    rw [Params.thresh, hδP]
    exact le_max_left _ _
  have hT2 : 6 * (Real.log (6 / T.δ) + Real.log T.P.m) ≤ T.P.thresh := by
    rw [Params.thresh, hδP]
    exact le_max_right _ _
  have hsum := numlattice_failure_le (ε := T.P.epsPrime) (Thresh := T.P.thresh)
    (δ := T.δ) (m := (T.P.m : ℝ)) (lamStar := lamStar)
    (errSum := ∑ t ∈ Finset.range jstar,
      2 * Real.exp (-(T.P.epsPrime ^ 2 * (lamStar * 2 ^ t) / 3)))
    (noiseSum := (T.P.m : ℝ) * Real.exp (-(T.P.thresh / 6)))
    (volSum := T.δ / 2)
    jstar (fun t => 2 * Real.exp (-(T.P.epsPrime ^ 2 * (lamStar * 2 ^ t) / 3)))
    hδ0 T.hδ1 T.P.epsPrime_pos T.epsPrime_lt_one hm hT1 hT2 hlam
    (fun _ => le_rfl) le_rfl le_rfl le_rfl
  -- so the failure probability is at most `δ`
  have hbad : (T.μ goodᶜ).toReal ≤ T.δ := le_trans hcover hsum
  -- and the good event therefore has probability at least `1 − δ`
  have hcov : (T.μ Set.univ).toReal ≤ (T.μ good).toReal + (T.μ goodᶜ).toReal := by
    have hsub : T.μ Set.univ ≤ T.μ good + T.μ goodᶜ := by
      rw [← Set.union_compl_self good]
      exact measure_union_le _ _
    calc (T.μ Set.univ).toReal ≤ (T.μ good + T.μ goodᶜ).toReal :=
          ENNReal.toReal_mono (by finiteness) hsub
      _ = (T.μ good).toReal + (T.μ goodᶜ).toReal :=
          ENNReal.toReal_add (measure_ne_top _ _) (measure_ne_top _ _)
  have huniv : (T.μ Set.univ).toReal = 1 := by
    rw [measure_univ, ENNReal.toReal_one]
  rw [huniv] at hcov
  linarith

end TtcProb

end Ttc

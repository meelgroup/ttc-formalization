import Ttc.Constants.Parameters
import Ttc.Lattice.Assembled
import Arlib.Lattice.KV97.Defs

/-!
# The KV97 rounding inflation is thin at TTC precision

The sampler uses `cOf epsPrime`, whereas the lattice/nonconvexity parameter block
uses the slightly larger logarithm in `Params.kappa`.  This file records the
comparison and converts the precision guarantee into the `κ/γ ≤ 1/n` hypothesis
of KV97 Lemma 1.
-/

namespace Ttc

open scoped ENNReal

/-- `cOf (ε/12)` uses `log (48/ε)`, while the first summand of the TTC
nonconvexity displacement uses the larger `log (64/ε)`. -/
theorem kv97_kappaOf_epsPrime_le_kappa (P : Params) :
    Arlib.KV97.kappaOf (Arlib.KV97.cOf P.epsPrime) P.r ≤ P.kappa := by
  have heps : 0 < P.ε := P.hε0
  have hepsPrime : 0 < P.epsPrime := P.epsPrime_pos
  have hfrac : 4 / P.epsPrime ≤ 8 / P.eta := by
    rw [Params.epsPrime, Params.eta]
    field_simp
    linarith
  have hlog : Real.log (4 / P.epsPrime) ≤ Real.log (8 / P.eta) := by
    exact Real.log_le_log (div_pos (by norm_num) hepsPrime) hfrac
  have hsqrt : Real.sqrt (2 * Real.log (4 / P.epsPrime)) ≤
      Real.sqrt (2 * Real.log (8 / P.eta)) := by
    exact Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_left hlog (by norm_num))
  unfold Arlib.KV97.kappaOf Arlib.KV97.cOf Params.kappa
  linarith

/-- At the precision chosen by TTC, the actual KV97 rounding displacement is at
most `1/n` of the dilated inradius.  This is the exact thin-inflation premise of
the `1/8` acceptance theorem. -/
theorem kv97_kappaOf_epsPrime_div_scaledRadius_le (P : Params)
    {gammaHat : Real} (hgammaHat : 0 < gammaHat) :
    Arlib.KV97.kappaOf (Arlib.KV97.cOf P.epsPrime) P.r /
        (latticeScale (P.precision gammaHat) * gammaHat) ≤
      1 / (P.n : Real) := by
  have hn : (0 : Real) < P.n := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one P.hn)
  have hm : (1 : Real) ≤ P.m := by exact_mod_cast P.hm
  have heta : P.eta ≤ 1 := P.eta_le_one
  have hgamma : 0 < P.gamma := P.gamma_pos
  have hscaled : 0 < latticeScale (P.precision gammaHat) * gammaHat :=
    mul_pos (latticeScale_pos _) hgammaHat
  have hscale : P.gamma ≤ latticeScale (P.precision gammaHat) * gammaHat :=
    gamma_le_latticeScale_mul P hgammaHat
  have hk0 : 0 ≤ Arlib.KV97.kappaOf (Arlib.KV97.cOf P.epsPrime) P.r :=
    Arlib.KV97.kappaOf_nonneg Arlib.KV97.cOf_nonneg
  have hthinP : P.kappa / P.gamma ≤ 1 / (P.n : Real) := by
    refine P.kappa_div_gamma_le.trans ?_
    rw [div_le_div_iff₀ (by positivity) hn]
    nlinarith
  calc
    Arlib.KV97.kappaOf (Arlib.KV97.cOf P.epsPrime) P.r /
          (latticeScale (P.precision gammaHat) * gammaHat)
        ≤ Arlib.KV97.kappaOf (Arlib.KV97.cOf P.epsPrime) P.r / P.gamma := by
          exact div_le_div_of_nonneg_left hk0 hgamma hscale
    _ ≤ P.kappa / P.gamma := by
      exact div_le_div_of_nonneg_right (kv97_kappaOf_epsPrime_le_kappa P) hgamma.le
    _ ≤ 1 / (P.n : Real) := hthinP

#print axioms kv97_kappaOf_epsPrime_le_kappa
#print axioms kv97_kappaOf_epsPrime_div_scaledRadius_le

end Ttc

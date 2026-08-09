/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import Ttc.Witness.TwoCube

/-!
# `Exec/Statement`: the capstone with the AllSAT call and `GetPrecision` inlined

`Ttc.ttc_volume_stmt` is `Ttc.ttc_volume_final` (`Exec/Final.lean`) with its
converter binder removed.  The repository owner's request was:

> The theorem's accuracy statement should not have `toDNF` and `precision` as
> inputs.  Instead of `toDNF` it should only take `M` and `φ`.  Precision should be
> the output of `GetPrecision`.

Both halves, and what actually changed:

* **`precision` was already not an input.**  `Ttc.ttc_volume_final` binds no `ρ`;
  every occurrence of the precision in its statement is `P.precision gammaHat`, and
  `Ttc.Params.precision` (`Model/Prelude.lean:310`) is
  `⌈Real.logb 10 (P.gamma / gammaHat)⌉` — literally `GetPrecision`, `alg:prec`
  line 91 / `alg:ttc` line 17.  Nothing here changes that; it is restated verbatim.
* **`toDNF` was an input, and now is not.**  `Ttc.ttc_volume_final` binds a
  converter `toDNF : BForm A → DNF A` together with `isDNF : IsDNFOf (toDNF φ) φ`
  and `isPositive : DNF.IsPositive (toDNF φ)`.  Here the converter is pinned to the
  development's own `Ttc.toDNF` (`Model/Prelude.lean:133`), `isDNF` is discharged
  outright by `Ttc.toDNF_isDNFOf`, and `isPositive` is discharged by
  `Ttc.toDNF_isPositive` from a hypothesis on the **input formula**.

## The one hypothesis that survives the substitution, and why

`Ttc.toDNF_isPositive` is *not* unconditional: at polarity `false` the converter must
emit negative literals (`Ttc.dnfAux`'s `.neg` case flips the polarity), so a formula
containing a negation has a DNF with a negated literal, and a negated atom denotes an
**open** half-space, which the counting side cannot use (README finding 5).  What
survives is therefore

```
hφ : φ.IsPositive
```

— `Ttc.BForm.IsPositive`, a syntactic, inspection-checkable condition on the *input
formula* `φ`, not a binder for an external tool and not an assumption about the
converter's output.  This is the honest residue: **two binders about `toDNF φ` are
replaced by one binder about `φ`.**

## What did *not* become derivable

* **`hlen` stays.**  `hlen : ((toDNF φ).length : ℝ) ≤ P.m` with
  `P.m = Nat.card {c // c ∈ toDNF φ}` is a `Nodup` condition on the cube list, and
  `Ttc.toDNF` is **provably not** duplicate-free: `Ttc.toDNF_length_gt_card_cubes`
  below exhibits the positive formula `a ∨ a`, whose DNF is `[[a], [a]]` — length
  `2`, one distinct cube — so `hlen` is `(2 : ℝ) ≤ 1`, false.  Pinning the converter
  cannot discharge it; a caller must supply it (every witness in the development
  does, by computing the length and the count).
* **`hr` stays, and is genuinely necessary.**
  `hr : 1 ≤ Nat.card (FacetIndex (toDNF φ))` fails for `φ = BForm.tt`, which is
  positive and has `toDNF φ = [[]]`: one cube, no literals, so
  `FacetIndex (toDNF φ) = Σ c, {l // l ∈ c.val}` is empty.
* **`hm` stays.**  `hm : 1 ≤ Nat.card {c // c ∈ toDNF φ}` is plausibly a consequence
  of `hφ` (at polarity `true` the converter's positive cases never return `[]`), but
  it is *not* derived here: it is an explicit argument of `ttcParams` inside `hP`, so
  it must be in scope in any case, and no attempt was made to remove it.  Do not read
  this file as claiming `hm` is redundant.

## Costs, stated with the result

Unchanged from `Ttc.ttc_volume_final`, because this is that theorem:

* **Exponential in the dimension, on both routes.**
  `Ttc.VolumeAlgorithm.monteCarlo` is hit-and-miss Monte Carlo at `Θ(Rⁿ/(ε²p))`
  samples and the ball walk's certified step count is `2^Θ(n)·log(M·Vol(P′)/ε′)`.
  The `runCost` conjunct is `alg:ttc`'s *charged* cost `m·(C_vol + C_sample·Thresh)`,
  not a polynomial-time claim; `thm:runtime` stays out of scope.  *Unconditional* and
  *efficient* are independent claims and only the first is established.
* **The `δ` split.**  `1 − δ` is the user's `δ`; every other occurrence is at the
  internal `δ₀ = 4δ/5` (so `P.deltaPrime = δ/(5m)`), which reprices the analysis
  rather than improving it — see `Exec/Final.lean`'s module docstring.
* **The sampler is not proved to differ from uniform.**  `law_tv` is a theorem, so no
  accuracy assumption is made, but distinctness of the finite-time iterate from
  `Arlib.uniformOn` is not proved.

## Non-vacuity

`Ttc.TwoCube.ttc_volume_stmt_two_cube` instantiates `Ttc.ttc_volume_stmt` on the
**two-cube** DNF of `Ttc/Witness/TwoCube.lean` at every `(ε, δ) ∈ (0,1]²`, and
`Ttc.TwoCube.ttc_volume_stmt_two_cube_at` pins it at two structurally different
parameter pairs — `(ε, δ) = (1/3, 9/10)` and `(1/2, 1/4)`, giving different sides,
precisions, corners and parameter blocks — with the achieved bounds `1/10` and `3/4`
proved **strictly positive inside the statement**, so neither conclusion is the
vacuous `0 ≤ (…).toReal`.  The transfer is direct: that witness already builds its
DNF with the canonical `Ttc.toDNF` and already discharges `isPositive` through
`Ttc.toDNF_isPositive twoForm_isPositive`, so `twoForm_isPositive` is exactly the
`hφ` this statement asks for.
-/

namespace Ttc

open MeasureTheory Set Pointwise

section Stmt

variable {A : Type*} {n : ℕ}

/-- **`thm:volumettc`, with the AllSAT call pinned and `GetPrecision` inlined.**

`Ttc.ttc_volume_final` with **no converter binder**: `toDNF` is the development's own
`Ttc.toDNF`, `isDNF` is gone (`Ttc.toDNF_isDNFOf`), `isPositive` is gone, replaced by
`hφ : φ.IsPositive` — a condition on the *input formula* (`Ttc.toDNF_isPositive`).
No `ρ` is bound: the precision is `P.precision gammaHat`, i.e. `GetPrecision`'s output
`⌈log₁₀(γ/γ̂)⌉` (`alg:ttc` line 17).  The conclusion is `Ttc.ttc_volume_final`'s,
verbatim, at `toDNF := Ttc.toDNF`.

The accuracy conjunct is `Pr[ output ∈ (1±ε)·Vol(F) ] ≥ 1 − δ` in the **user's** `δ`;
the runtime conjunct is `alg:ttc`'s charged cost `m·(C_vol + C_sample·Thresh)`.

**Costs.** Exponential in `n` on both routes: `Θ(Rⁿ/(ε²p))` Monte-Carlo samples for
the volume estimator and `2^Θ(n)·log(M·Vol(P′)/ε′)` certified ball-walk steps, with
the lattice transcription enumerating `Ttc.latticeCount` points.  This is a
correctness statement, not an efficiency one; `thm:runtime` is out of scope.

**`hlen` is not free**: it is a `Nodup` condition and `Ttc.toDNF` is provably not
duplicate-free — see `Ttc.toDNF_length_gt_card_cubes`. -/
theorem ttc_volume_stmt
    (atoms : A → LinAtom n) (φ : BForm A) (ε δ : ℝ)
    (hε0 : 0 < ε) (hε1 : ε ≤ 1) (hδ0 : 0 < δ) (hδ1 : δ ≤ 1) (hn : 1 ≤ n)
    (M : A → Set (Space n)) (M_eq : M = fun a => (atoms a).halfspace)
    (hφ : φ.IsPositive)
    (hm : 1 ≤ Nat.card {c : Cube A // c ∈ toDNF φ})
    (hr : 1 ≤ Nat.card (FacetIndex (toDNF φ)))
    (P : Params) (hP : P = ttcParams (toDNF φ) n ε (4 * δ / 5) hε0 hε1 hn hm hr)
    (hlen : ((toDNF φ).length : ℝ) ≤ P.m)
    (hbdd : Bornology.IsBounded (sol M φ))
    (hcoeff : ∀ j : FacetIndex (toDNF φ), (atoms j.2.val.atom).coeff ≠ 0)
    (cen : {c : Cube A // c ∈ toDNF φ} → Space n) (gammaHat : ℝ) (hgammaHat : 0 < gammaHat)
    (ball_subset : ∀ i, Metric.ball (cen i) gammaHat ⊆ region M i.val)
    (big : ∀ c ∈ mcGood M (toDNF φ) cen gammaHat P.epsPrime P.deltaPrime,
      (1 - P.epsPrime) * P.thresh / 8
        ≤ ∑ s, rates M φ (toDNF φ) (P.precision gammaHat)
            (e2eSampD M (toDNF φ) (P.precision gammaHat) P.epsPrime (canonRfac (toDNF φ))
              (Jt := Fin (Nat.card (FacetIndex (toDNF φ)))) (canonAm atoms (toDNF φ))
              (canonBv atoms (toDNF φ) (latticeScale (P.precision gammaHat)))
              cen gammaHat (canonDm M (toDNF φ) (P.precision gammaHat)))
            (mcVol M (toDNF φ) cen gammaHat P.epsPrime P.deltaPrime c) s) :
    (1 - δ ≤
      (∫⁻ c, trajLaw (rates M φ (toDNF φ) (P.precision gammaHat)
            (e2eSampD M (toDNF φ) (P.precision gammaHat) P.epsPrime (canonRfac (toDNF φ))
              (Jt := Fin (Nat.card (FacetIndex (toDNF φ)))) (canonAm atoms (toDNF φ))
              (canonBv atoms (toDNF φ) (latticeScale (P.precision gammaHat)))
              cen gammaHat (canonDm M (toDNF φ) (P.precision gammaHat)))
            (mcVol M (toDNF φ) cen gammaHat P.epsPrime P.deltaPrime c))
          {t : ℕ → Fin (latticeCount M φ (P.precision gammaHat)) → ℕ |
            ttcOutput P (coveredOracles M φ (P.precision gammaHat)
                (mcVol M (toDNF φ) cen gammaHat P.epsPrime P.deltaPrime c))
                toDNF (P.precision gammaHat) φ t
              ∈ relErr ε (volSol M φ)}
        ∂(MonteCarlo.coins n)).toReal)
    ∧
    (∀ (c : ℕ → Space n)
        (t : ℕ → Fin (latticeCount M φ (P.precision gammaHat)) → ℕ)
        (cVol cSample thr : ℕ),
      (thr : ℝ) = P.thresh →
      Terminates P (coveredOracles M φ (P.precision gammaHat)
          (mcVol M (toDNF φ) cen gammaHat P.epsPrime P.deltaPrime c) t) (toDNF φ) →
      runCost P (coveredOracles M φ (P.precision gammaHat)
            (mcVol M (toDNF φ) cen gammaHat P.epsPrime P.deltaPrime c) t)
          cVol cSample (P.precision gammaHat) (toDNF φ)
        ≤ (toDNF φ).length * (cVol + cSample * thr)) :=
  ttc_volume_final atoms φ ε δ hε0 hε1 hδ0 hδ1 hn M M_eq toDNF
    (toDNF_isDNFOf φ) (toDNF_isPositive hφ) hm hr P hP hlen hbdd hcoeff
    cen gammaHat hgammaHat ball_subset big

end Stmt

/-! ## Why `hlen` could not be discharged

`hlen` is a duplicate-freeness condition in disguise (`Exec/Final.lean`'s module
docstring), so it would vanish if `Ttc.toDNF` always returned a `Nodup` list.  It does
not, and the counterexample is a two-line positive formula. -/

/-- **`Ttc.toDNF` is not duplicate-free, so `hlen` is a real hypothesis.**

For the positive formula `a ∨ a`, `Ttc.toDNF` returns the cube `[a]` **twice**: the
list has length `2` while the DNF has one distinct cube.  Hence `ttc_volume_stmt`'s
`hlen : ((toDNF φ).length : ℝ) ≤ P.m` — with `P.m = Nat.card {c // c ∈ toDNF φ}` from
`Ttc.ttcParams` — is `(2 : ℝ) ≤ 1`, which is false: pinning the converter to
`Ttc.toDNF` cannot discharge `hlen`. -/
theorem toDNF_length_gt_card_cubes {A : Type*} (a : A) :
    ∃ φ : BForm A, φ.IsPositive ∧
      ¬ (toDNF φ).Nodup ∧
      ¬ (((toDNF φ).length : ℝ) ≤ (Nat.card {c : Cube A // c ∈ toDNF φ} : ℝ)) := by
  refine ⟨(BForm.atom a).or (BForm.atom a), ⟨trivial, trivial⟩, ?_, ?_⟩
  · show ¬ ([[⟨a, true⟩], [⟨a, true⟩]] : DNF A).Nodup
    simp
  · have hcard : Nat.card {c : Cube A // c ∈ ([[⟨a, true⟩], [⟨a, true⟩]] : DNF A)} = 1 := by
      refine Nat.card_eq_one_iff_exists.2 ⟨⟨[⟨a, true⟩], by simp⟩, ?_⟩
      rintro ⟨y, hy⟩
      simp only [List.mem_cons, List.not_mem_nil, or_self, or_false] at hy
      exact Subtype.ext hy
    show ¬ ((([[⟨a, true⟩], [⟨a, true⟩]] : DNF A).length : ℝ)
      ≤ (Nat.card {c : Cube A // c ∈ ([[⟨a, true⟩], [⟨a, true⟩]] : DNF A)} : ℝ))
    rw [hcard]
    norm_num

namespace TwoCube

/-! ## Non-vacuity: the two-cube witness transfers unchanged

`Ttc.TwoCube.ttc_volume_final_two_cube` already applies `Ttc.ttc_volume_final` at
`toDNF := Ttc.toDNF` with `isPositive` supplied as
`Ttc.toDNF_isPositive twoForm_isPositive`.  So `hφ := twoForm_isPositive` is exactly
what `Ttc.ttc_volume_stmt` needs, and the same argument list — minus the converter and
its two properties — instantiates the new statement. -/

/-- **`Ttc.ttc_volume_stmt` on a DNF with two cubes**, at every `(ε, δ) ∈ (0,1]²`.

The witness is the pair of disjoint boxes `[0,c]ⁿ` and `[lo, lo+c]ⁿ` of
`Ttc/Witness/TwoCube.lean`; its DNF has two cubes
(`Ttc.TwoCube.card_toDNF_eq_two`), so `m = 2` and the per-cube error composition, the
two-call union bound behind `deltaPrime = δ/(4m)`, and a `∑ s` over lattice points of
two different regions with different ball centres are all exercised.

**Cost — exponential in `n`, and paid twice.**  The volume estimator is hit-and-miss
Monte Carlo at `Θ(Rⁿ/(ε'²δ'))` samples per cube, the ball walk's certified step count
is `2^Θ(n)·log(M·Vol(P′)/ε′)`, and the transcription enumerates `Θ((c·10^ρ)ⁿ)` lattice
points; with `m = 2` each is paid twice and the charged bound
`m·(C_vol + C_sample·Thresh)` grows with `m`.  Unconditional correctness, not
efficiency. -/
theorem ttc_volume_stmt_two_cube (n : ℕ) (hn : 1 ≤ n) (ε δ : ℝ)
    (hε0 : 0 < ε) (hε1 : ε ≤ 1) (hδ0 : 0 < δ) (hδ1 : δ ≤ 1) :
    (1 - δ ≤ twoAcc n hn ε (4 * δ / 5) hε0 hε1)
    ∧
    (∀ (c : ℕ → Space n)
        (t : ℕ → Fin (latticeCount (MTT n hn ε (4 * δ / 5) hε0 hε1) (twoForm n)
          (rhoT n hn ε (4 * δ / 5) hε0 hε1)) → ℕ)
        (cVol cSample thr : ℕ),
      (thr : ℝ) = (parT n hn ε (4 * δ / 5) hε0 hε1).thresh →
      Terminates (parT n hn ε (4 * δ / 5) hε0 hε1)
          (coveredOracles (MTT n hn ε (4 * δ / 5) hε0 hε1) (twoForm n)
            (rhoT n hn ε (4 * δ / 5) hε0 hε1) (volT n hn ε (4 * δ / 5) hε0 hε1 c) t)
          (Ttc.toDNF (twoForm n)) →
      runCost (parT n hn ε (4 * δ / 5) hε0 hε1)
          (coveredOracles (MTT n hn ε (4 * δ / 5) hε0 hε1) (twoForm n)
            (rhoT n hn ε (4 * δ / 5) hε0 hε1) (volT n hn ε (4 * δ / 5) hε0 hε1 c) t)
          cVol cSample (rhoT n hn ε (4 * δ / 5) hε0 hε1) (Ttc.toDNF (twoForm n))
        ≤ (Ttc.toDNF (twoForm n)).length * (cVol + cSample * thr)) := by
  have h0 : (0 : ℝ) < 4 * δ / 5 := by linarith
  have h1 : (4 : ℝ) * δ / 5 ≤ 1 := by linarith
  exact ttc_volume_stmt (atomsT n hn ε (4 * δ / 5) hε0 hε1) (twoForm n) ε δ
    hε0 hε1 hδ0 hδ1 hn (MTT n hn ε (4 * δ / 5) hε0 hε1) rfl
    twoForm_isPositive
    (one_le_card_cubes_two hn) (one_le_card_facets_two hn)
    (parT n hn ε (4 * δ / 5) hε0 hε1) rfl
    (by rw [length_toDNF_twoForm, parT_m])
    (isBounded_sol_T n hn ε (4 * δ / 5) hε0 hε1)
    (coeff_ne_zero_two _ _)
    (cenT n hn ε (4 * δ / 5) hε0 hε1) (gamT n hn ε (4 * δ / 5) hε0 hε1)
    (gamT_pos n hn ε (4 * δ / 5) hε0 hε1) (ball_subset_two n hn ε (4 * δ / 5) hε0 hε1)
    (fun c hc => big_two n hn ε (4 * δ / 5) hε0 hε1 h0 h1 c hc)

/-- **The two-cube guarantee of `Ttc.ttc_volume_stmt`, on the named probability.** -/
theorem two_cube_stmt_acc_ge (n : ℕ) (hn : 1 ≤ n) (ε δ : ℝ)
    (hε0 : 0 < ε) (hε1 : ε ≤ 1) (hδ0 : 0 < δ) (hδ1 : δ ≤ 1) :
    1 - δ ≤ twoAcc n hn ε (4 * δ / 5) hε0 hε1 :=
  (ttc_volume_stmt_two_cube n hn ε δ hε0 hε1 hδ0 hδ1).1

/-- **`Ttc.ttc_volume_stmt` on a two-cube DNF at two structurally different parameter
pairs, with the achieved bound a positive numeral.**

* `(ε, δ) = (1/3, 9/10)`: bound `1/10 > 0`, at a `δ ∈ (4/5, 1)` where
  `Ttc.ttc_volume_endToEnd`'s budget `1 − δ − δ/4 = −1/8` certifies nothing.
* `(ε, δ) = (1/2, 1/4)`: a different accuracy *and* confidence, so the two runs have
  different sides `Ttc.TwoCube.sideT`, different precisions `Ttc.TwoCube.rhoT`,
  different corners `Ttc.TwoCube.loT` and different parameter blocks
  `Ttc.TwoCube.parT` — genuinely two instances, not one instance twice.

Both numerals are proved strictly positive **in the statement**, so neither conclusion
is the vacuous `0 ≤ (…).toReal`.  Both runs carry the exponential cost of
`Ttc.TwoCube.ttc_volume_stmt_two_cube`, twice over. -/
theorem ttc_volume_stmt_two_cube_at (n : ℕ) (hn : 1 ≤ n)
    (hε₁ : (0 : ℝ) < 1/3) (hε₁' : (1/3 : ℝ) ≤ 1)
    (hε₂ : (0 : ℝ) < 1/2) (hε₂' : (1/2 : ℝ) ≤ 1) :
    ((0 : ℝ) < 1/10 ∧ (1/10 : ℝ) ≤ twoAcc n hn (1/3) (4 * (9/10) / 5) hε₁ hε₁'
      ∧ (4/5 : ℝ) < 9/10 ∧ (9/10 : ℝ) < 1)
    ∧ ((0 : ℝ) < 3/4 ∧ (3/4 : ℝ) ≤ twoAcc n hn (1/2) (4 * (1/4) / 5) hε₂ hε₂') := by
  refine ⟨⟨by norm_num, ?_, by norm_num, by norm_num⟩, ⟨by norm_num, ?_⟩⟩
  · have h := two_cube_stmt_acc_ge n hn (1/3) (9/10) hε₁ hε₁' (by norm_num) (by norm_num)
    linarith
  · have h := two_cube_stmt_acc_ge n hn (1/2) (1/4) hε₂ hε₂' (by norm_num) (by norm_num)
    linarith

/-- **The bound is a genuine number, not `ENNReal.toReal ⊤ = 0`.**  A strictly
positive lower bound on the `toReal` forces the measure itself to be nonzero and
finite. -/
theorem twoProb_stmt_pos_ne_top (n : ℕ) (hn : 1 ≤ n)
    (hε0 : (0 : ℝ) < 1/3) (hε1 : (1/3 : ℝ) ≤ 1) :
    0 < twoProb n hn (1/3) (4 * (9/10) / 5) hε0 hε1
      ∧ twoProb n hn (1/3) (4 * (9/10) / 5) hε0 hε1 ≠ ⊤ := by
  have h := (ttc_volume_stmt_two_cube_at n hn hε0 hε1 (by norm_num) (by norm_num)).1.2.1
  have hpos : 0 < (twoProb n hn (1/3) (4 * (9/10) / 5) hε0 hε1).toReal :=
    lt_of_lt_of_le (by norm_num : (0:ℝ) < 1/10) h
  exact ⟨(ENNReal.toReal_pos_iff.1 hpos).1, (ENNReal.toReal_pos_iff.1 hpos).2.ne⟩

end TwoCube

end Ttc

/-! ## Axiom profile

Every declaration of this file, checked transitively (`CLAUDE.md` §4).  Expect
`[propext, Classical.choice, Quot.sound]` throughout — no `sorry`, no custom axiom,
no `native_decide`. -/

#check @Ttc.ttc_volume_stmt

#print axioms Ttc.ttc_volume_stmt
#print axioms Ttc.toDNF_length_gt_card_cubes
#print axioms Ttc.TwoCube.ttc_volume_stmt_two_cube
#print axioms Ttc.TwoCube.two_cube_stmt_acc_ge
#print axioms Ttc.TwoCube.ttc_volume_stmt_two_cube_at
#print axioms Ttc.TwoCube.twoProb_stmt_pos_ne_top

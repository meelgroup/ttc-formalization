/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import Ttc.Exec.Complexity
import Ttc.Sampler.Construct
import Ttc.Volume.MonteCarlo

/-!
# `CostModel`: what `cVol` and `cSample` denote

`Ttc.stepCost cVol cSample N = cVol + cSample * N` (`Model/Pseudocode`) is the whole of
this development's notion of cost, and until this file `cVol` and `cSample` denoted
**nothing**: `Ttc.runCost_le` is true at every pair of naturals, including wrong ones,
because no theorem anywhere related either number to anything a subroutine does.  A
mixing-time bound — "the chain is within TV `eps` of stationary after `t` steps" — could
therefore not be turned into a price, because nothing said the algorithm *takes* those
steps.

This file supplies the missing layer: two *derived* cost quantities, each defined as an
infimum over the budgets at which the **constructed** subroutine's own definition already
satisfies a property, and each with at least one proved instance at a constructed object.
Neither is a field of a structure and neither asserts a running time.

## The two notions

**1. `Ttc.coinCost` — the coin-query cost of the volume oracle.**  `Ttc.ReadsAtMost f k`
says `f` agrees on any two coin sequences agreeing below `k`; `Ttc.coinCost f` is the least
such `k` (`⊤` if there is none).  This is the standard *query complexity in the randomness
oracle*, and it is genuinely operational: it is falsifiable (`Ttc.succ_le_coinCost` proves
lower bounds from two coin sequences with different outputs), compositional
(`Ttc.ReadsAtMost.map`, `.comp₂`, `.finsetSum`, `.dite`, grounded at
`Ttc.readsAtMost_eval`, "reading coin `i` costs `i+1`"), and it takes the value `⊤`
(`Ttc.coinCost_firstAccept`) on a loop with no worst-case round count.

**2. `Ttc.mixCost` — the step-budget cost of the sampler's chain.**  `Ttc.mixCost K δ mu0 π
eps` is the least `t` at which `Ttc.ballWalkLaw K δ mu0 t` is within `eps` of `π` in total
variation, `⊤` if no budget works.  This is *not* "the chain takes `t` steps", which is
true by definition of an iterate and therefore vacuous.  It is the least budget at which
the constructed law meets its own accuracy specification — which is exactly where a mixing
theorem attaches, as an **upper bound** on it.

## The proved instances (nothing here is a naming convention)

* `Ttc.readsAtMost_est` — the Monte-Carlo estimator reads at most `Ttc.MonteCarlo.nSamp`
  coins, *derived* from the closure lemmas rather than restated.
* `Ttc.coinCost_est_eq` — and **exactly** that many, on any body with one hit and one miss:
  the derived cost equals `nSamp` on the nose.  `Ttc.coinCost_est_unitBall` instantiates it
  at the unit ball in dimension `n ≥ 1`, using the same hull witness as the anti-cheat
  `Ttc.MonteCarlo.est_ne_volume`.  So the notion is not vacuous and the bound is tight.
* `Ttc.coinCost_mcVol_le`, `Ttc.coinCost_ttcVol_le` — the constructed `Vol_ED`, and the
  `vol` field of the run's own oracle bundle, cost at most `Ttc.mcVolCoins` /
  `Ttc.ttcVolCoins` coins.  This is what turns `Exec/Complexity` §4's *pricing convention*
  into a derived statement: the price list charged there dominates the derived cost.
* `Ttc.mixCost_le_mixSteps` — the ball walk on the Kannan–Vempala inflated polytope meets
  its TV specification by budget `Ttc.mixSteps`, i.e. `Ttc.mixSteps` is an upper bound on
  the derived step cost.  `Ttc.mixCost_le_e2eBallWalkSteps` is the same at the exact
  arguments `Ttc.e2eSampD` supplies (`Ttc.e2eSampD_eq_ballWalk`).
* `Ttc.one_le_mixCost_dirac` — `Ttc.mixCost` is not identically `0`: from a start that is
  not the target, at least one step is needed.
* `Ttc.ballWalkLaw_add` — the budget is a *budget*: `s + t` steps is `s` steps then `t`
  more from wherever that got to.  Resumption, not decoration.

## What could NOT be modelled, and why — read this before quoting anything above

**The sampler's rejection rounds have no cost in either notion, and this is not an
oversight.**  `Ttc.kv97SampD` is a *density*: a function `Cube A → Space n → ℝ` built from
integrals against the continuous law.  It consumes no coin sequence, so `Ttc.ReadsAtMost`
does not typecheck for it, and it is not a family of measures indexed by a budget, so
`Ttc.mixCost` does not apply either.  There is no object in this development that performs
the rejection loop, so there is nothing here whose cost could be derived.  What *is* true
of such a loop is `Ttc.coinCost_firstAccept`: the round count of the model rejection loop
`Ttc.firstAccept` defined below has `coinCost = ⊤` — no finite prefix of coins determines
it.  That theorem is about `Ttc.firstAccept`, a function defined here, and is **not** a
theorem about `Ttc.kv97SampD`; it is included to show that the cost model can express
"unbounded", and to record what shape the sampler's missing cost has.

So the honest summary is an **asymmetry**:

| subroutine | constructed as | derived cost | status |
| --- | --- | --- | --- |
| `Vol_ED` | `Ttc.mcVol`, a function of coins | `Ttc.coinCost` | derived, and *exact* on a witness |
| sampler, chain part | `Ttc.ballWalkLaw`, a budgeted family of measures | `Ttc.mixCost` | derived, upper-bounded by `Ttc.mixSteps` |
| sampler, rejection part | `Ttc.kv97SampD`, a density | — | **not modellable**: no coin-consuming object exists |
| the `while` loops of `alg:ttc` 32–42 | `Ttc.trajThin`/`Ttc.trajPois` read-offs of a row `Fin L → ℕ` | — | out of scope here; the index type is not `ℕ → α` |

**Neither notion is a running time.**  `Ttc.coinCost` counts coins, not machine
operations: the arithmetic inside a coin test is free, and so is everything the rejection
loop does.  `Ttc.mixCost` counts chain steps, and the arithmetic inside a ball-walk step is
free.  A bound on either is a bound on a *query count*, and this file says nothing about
`thm:runtime`'s `O(m·n⁴)`, which remains out of scope.

**Can `cVol`/`cSample` be given values now?**  In principle, yes, and the shape is now
fixed.  `cVol` at cube `i` denotes `Ttc.coinCost (fun c => (ttcOracleBundle … c t).vol i)`,
which `Ttc.coinCost_ttcVol_le` bounds by `Ttc.ttcVolCoins`, and which
`Ttc.coinCost_est_eq` shows is *exactly* `Ttc.MonteCarlo.nSamp` whenever the cube's body
has a hit and a miss.  `cSample` denotes `Ttc.mixCost` at the sampler's geometry, which
`Ttc.mixCost_le_e2eBallWalkSteps` bounds by `Ttc.mixSteps`.  A KV97 or Hit-and-Run mixing
theorem lands as a *smaller* upper bound on the latter — that is the attachment point, and
it exists now.

**`cVol` has since been given a value, and `cSample` has not.**  `Ttc.MonteCarlo.rad` is
now the infimum of the enclosing radii rather than a `Classical.choice`, so
`Ttc.MonteCarlo.nSamp_roundBody_le` (`Volume/RadBound`) is an unconditional closed form,
and `Ttc.ttcVolCoins_le_ttcVolPrice` (`Exec/PriceList`) makes it uniform over the DNF's
cubes.  ⚠ This paragraph used to add that `Ttc.ttc_volume_estimate` "carries that number
in place of its old `cVol` binder" — **false when written and still false** (corrected
2026-08-12).  The headline now carries the *Cousins–Vempala* price in that slot, which is
a modelling choice rather than a bound on `Ttc.ttcVolCoins`; `Ttc.ttcVolPrice` is the
number this file's argument actually justifies.  See `Ttc/Exec/PricedHeadline.lean`.
No uniform bound on `Ttc.mixCost` at the run's cubes is available — see
`Exec/PriceList`'s docstring for the exact residue — so nothing dominates the headline's
sampling slot either.  And
the rejection rounds remain uncounted whatever is substituted, so the *total* is still an
undercount.  `Ttc/Model/ProblemSetting.lean` is untouched.
-/

namespace Ttc

open MeasureTheory

open scoped ENNReal

/-! # §1  The coin-query cost model

`Ttc.ReadsAtMost` and its closure lemmas.  Nothing in this section mentions `TTC`; it is a
statement about arbitrary functions of a coin sequence.  The point of the closure lemmas is
that the cost of a compound subroutine is *computed* from the costs of its parts, so that
`Ttc.readsAtMost_est` below is a derivation rather than a restatement. -/

section Reads

variable {α β γ ζ : Type*}

/-- **`f` reads at most `k` coins**: any two coin sequences agreeing on the first `k`
coordinates give the same output.

This is the one operational notion in this development that is *derivable from a
definition* rather than assumed of it — `Ttc.mcVol_congr_of_agree` (`Exec/Complexity` §4)
is an instance of it, proved by unfolding the estimator's sum. -/
def ReadsAtMost (f : (ℕ → α) → β) (k : ℕ) : Prop :=
  ∀ c c' : ℕ → α, (∀ j < k, c j = c' j) → f c = f c'

/-- Reading more coins is a weaker claim. -/
theorem ReadsAtMost.mono {f : (ℕ → α) → β} {k k' : ℕ} (h : ReadsAtMost f k) (hk : k ≤ k') :
    ReadsAtMost f k' := fun c c' hcc => h c c' fun j hj => hcc j (lt_of_lt_of_le hj hk)

/-- A constant reads nothing. -/
theorem readsAtMost_const (b : β) : ReadsAtMost (fun _ : ℕ → α => b) 0 := fun _ _ _ => rfl

/-- **The grounding case**: looking at coin `i` costs `i + 1`.  Everything else in this
section is closure; without this lemma the notion would be satisfied by `k = 0`
everywhere. -/
theorem readsAtMost_eval (i : ℕ) : ReadsAtMost (fun c : ℕ → α => c i) (i + 1) :=
  fun _ _ h => h i (Nat.lt_succ_self i)

/-- Post-processing is free. -/
theorem ReadsAtMost.map {f : (ℕ → α) → β} {k : ℕ} (g : β → γ) (h : ReadsAtMost f k) :
    ReadsAtMost (fun c => g (f c)) k := fun c c' hcc => congrArg g (h c c' hcc)

/-- Two subroutines combined read the maximum of what each reads. -/
theorem ReadsAtMost.comp₂ {f : (ℕ → α) → β} {g : (ℕ → α) → γ} {k l : ℕ}
    (F : β → γ → ζ) (hf : ReadsAtMost f k) (hg : ReadsAtMost g l) :
    ReadsAtMost (fun c => F (f c) (g c)) (max k l) := by
  intro c c' hcc
  show F (f c) (g c) = F (f c') (g c')
  rw [hf c c' fun j hj => hcc j (lt_of_lt_of_le hj (le_max_left _ _)),
    hg c c' fun j hj => hcc j (lt_of_lt_of_le hj (le_max_right _ _))]

/-- A finite sum of subroutines, each reading at most `k`, reads at most `k`. -/
theorem ReadsAtMost.finsetSum {ι : Type*} [AddCommMonoid β] (s : Finset ι)
    (F : ι → (ℕ → α) → β) {k : ℕ} (h : ∀ i ∈ s, ReadsAtMost (F i) k) :
    ReadsAtMost (fun c => ∑ i ∈ s, F i c) k := fun c c' hcc =>
  Finset.sum_congr rfl fun i hi => h i hi c c' hcc

/-- A branch on a condition that does not depend on the coins reads what its branches
read.  This is what covers the `if i ∈ D` of `Ttc.mcVol`. -/
theorem ReadsAtMost.dite {p : Prop} [Decidable p] {f : p → (ℕ → α) → β}
    {g : ¬p → (ℕ → α) → β} {k : ℕ} (hf : ∀ hp, ReadsAtMost (f hp) k)
    (hg : ∀ hp, ReadsAtMost (g hp) k) :
    ReadsAtMost (fun c => dite p (fun hp => f hp c) (fun hp => g hp c)) k := by
  intro c c' hcc
  by_cases hp : p
  · simp only [dif_pos hp]; exact hf hp c c' hcc
  · simp only [dif_neg hp]; exact hg hp c c' hcc

/-! ## The derived cost

`Ttc.coinCost` is an infimum over the budgets that *work*, so it is a property of `f`'s
definition and cannot be chosen.  The `⊤` value is meaningful: it says no finite prefix of
the coins determines the output (`Ttc.coinCost_firstAccept`). -/

/-- **The coin cost of `f`**: the least `k` with `Ttc.ReadsAtMost f k`, and `⊤` if there is
none.  Valued in `ℕ∞` precisely so that "reads unboundedly many coins" is expressible. -/
noncomputable def coinCost (f : (ℕ → α) → β) : ℕ∞ :=
  ⨅ k : {k : ℕ // ReadsAtMost f k}, (k.1 : ℕ∞)

/-- Any working budget is an upper bound on the cost. -/
theorem coinCost_le {f : (ℕ → α) → β} {k : ℕ} (h : ReadsAtMost f k) :
    coinCost f ≤ (k : ℕ∞) :=
  iInf_le (fun k : {k : ℕ // ReadsAtMost f k} => (k.1 : ℕ∞)) ⟨k, h⟩

/-- Lower bounds on the cost come from lower bounds on every working budget. -/
theorem le_coinCost {f : (ℕ → α) → β} {m : ℕ∞} (h : ∀ k, ReadsAtMost f k → m ≤ (k : ℕ∞)) :
    m ≤ coinCost f := le_iInf fun k => h k.1 k.2

/-- **The falsifiability lemma.**  Exhibiting two coin sequences that agree below `k` and
give different outputs proves the cost is at least `k + 1`.  This is what makes
`Ttc.coinCost` a measurement rather than a bookkeeping device. -/
theorem succ_le_coinCost {f : (ℕ → α) → β} {k : ℕ} (h : ¬ ReadsAtMost f k) :
    ((k + 1 : ℕ) : ℕ∞) ≤ coinCost f := by
  refine le_coinCost fun j hj => ?_
  have hlt : k < j := by
    by_contra hcon
    exact h (hj.mono (not_lt.1 hcon))
  exact_mod_cast Nat.succ_le_of_lt hlt

/-- The cost is exactly `k + 1` when `k + 1` works and `k` does not. -/
theorem coinCost_eq_succ {f : (ℕ → α) → β} {k : ℕ} (h : ReadsAtMost f (k + 1))
    (h' : ¬ ReadsAtMost f k) : coinCost f = ((k + 1 : ℕ) : ℕ∞) :=
  le_antisymm (coinCost_le h) (succ_le_coinCost h')

/-- **Unbounded cost.**  If no budget works the cost is `⊤`. -/
theorem coinCost_eq_top {f : (ℕ → α) → β} (h : ∀ k, ¬ ReadsAtMost f k) : coinCost f = ⊤ := by
  haveI : IsEmpty {k : ℕ // ReadsAtMost f k} := ⟨fun k => h k.1 k.2⟩
  exact iInf_of_empty _

end Reads

/-! # §2  The volume oracle's coin cost, derived

The constructed `Vol_ED` is `Ttc.mcVol`, built from `Ttc.MonteCarlo.est`, which *is* a
function of a coin sequence.  So the coin model applies to it directly, and the cost comes
out of the closure lemmas of §1 rather than being asserted. -/

section Volume

variable {n : ℕ}

/-- The `i`-th score reads coin `i`, hence at most `i + 1` coins. -/
theorem readsAtMost_score (K : Set (Space n)) (i : ℕ) :
    ReadsAtMost (MonteCarlo.score K i) (i + 1) := by
  intro c c' h
  simp only [MonteCarlo.score, h i (Nat.lt_succ_self i)]

/-- **The estimator reads at most `Ttc.MonteCarlo.nSamp` coins** — *derived*, by
`Ttc.ReadsAtMost.finsetSum` over `Finset.range (nSamp …)` from `Ttc.readsAtMost_score`,
then `Ttc.ReadsAtMost.map` for the leading constant.  Compare
`Ttc.monteCarloEst_congr_of_agree` (`Exec/Complexity`), which is the same fact proved by
hand; the point of this proof is that the number is *computed* from the parts. -/
theorem readsAtMost_est (K : Set (Space n)) (ε pf : ℝ) :
    ReadsAtMost (MonteCarlo.est K ε pf) (MonteCarlo.nSamp K ε pf) := by
  have hsum : ReadsAtMost
      (fun c : ℕ → Space n =>
        ∑ i ∈ Finset.range (MonteCarlo.nSamp K ε pf), MonteCarlo.score K i c)
      (MonteCarlo.nSamp K ε pf) :=
    ReadsAtMost.finsetSum _ _ fun i hi =>
      (readsAtMost_score K i).mono (Finset.mem_range.1 hi)
  exact hsum.map (fun s => MonteCarlo.scale K / (MonteCarlo.nSamp K ε pf : ℝ) * s)

/-- **The estimator reads no fewer**, on any body with one hit and one miss: flipping the
last of the `nSamp` coins from a hit to a miss changes the estimate by
`Ttc.MonteCarlo.scale K / nSamp ≠ 0`.  Together with `Ttc.readsAtMost_est` this pins the
derived cost exactly. -/
theorem not_readsAtMost_est {K : Set (Space n)} (ε pf : ℝ) {xh xm : Space n}
    (hh : xh ∈ MonteCarlo.target K) (hm : xm ∉ MonteCarlo.target K) :
    ¬ ReadsAtMost (MonteCarlo.est K ε pf) (MonteCarlo.nSamp K ε pf - 1) := by
  classical
  obtain ⟨m, hm'⟩ : ∃ m, MonteCarlo.nSamp K ε pf = m + 1 :=
    ⟨MonteCarlo.nSamp K ε pf - 1,
      (Nat.succ_pred_eq_of_pos (MonteCarlo.nSamp_pos K ε pf)).symm⟩
  have hpred : MonteCarlo.nSamp K ε pf - 1 = m := by omega
  have hindh : MonteCarlo.ind K xh = 1 := by
    rw [MonteCarlo.ind, Set.indicator_of_mem hh]; rfl
  have hindm : MonteCarlo.ind K xm = 0 := by
    rw [MonteCarlo.ind, Set.indicator_of_notMem hm]
  intro hcon
  have hagree : ∀ j < MonteCarlo.nSamp K ε pf - 1,
      (fun _ : ℕ => xh) j = (fun j : ℕ => if j = m then xm else xh) j := by
    intro j hj
    rw [hpred] at hj
    simp only [if_neg (Nat.ne_of_lt hj)]
  have heq := hcon _ _ hagree
  -- the all-hit sequence gives `scale K`
  have hleft : MonteCarlo.est K ε pf (fun _ => xh) = MonteCarlo.scale K := by
    have hs : ∀ i ∈ Finset.range (MonteCarlo.nSamp K ε pf),
        MonteCarlo.score K i (fun _ => xh) = 1 := fun i _ => hindh
    rw [MonteCarlo.est, Finset.sum_congr rfl hs, Finset.sum_const, Finset.card_range,
      nsmul_eq_mul, mul_one, hm']
    have hd : ((m : ℝ) + 1) ≠ 0 := by positivity
    push_cast
    field_simp
  -- flipping the last coin to a miss gives `scale K / (m+1) * m`
  have hright : MonteCarlo.est K ε pf (fun j => if j = m then xm else xh)
      = MonteCarlo.scale K / ((m : ℝ) + 1) * (m : ℝ) := by
    have hs : ∀ i ∈ Finset.range m,
        MonteCarlo.score K i (fun j => if j = m then xm else xh) = 1 := by
      intro i hi
      simp only [MonteCarlo.score, if_neg (Nat.ne_of_lt (Finset.mem_range.1 hi))]
      exact hindh
    have hlast : MonteCarlo.score K m (fun j => if j = m then xm else xh) = 0 := by
      simp only [MonteCarlo.score]
      exact hindm
    rw [MonteCarlo.est, hm', Finset.sum_range_succ, Finset.sum_congr rfl hs, Finset.sum_const,
      Finset.card_range, nsmul_eq_mul, mul_one, hlast, add_zero]
    push_cast
    ring
  rw [hleft, hright] at heq
  have hspos := MonteCarlo.scale_pos K
  have hd : ((m : ℝ) + 1) ≠ 0 := by positivity
  rw [div_mul_eq_mul_div, eq_div_iff hd] at heq
  nlinarith [hspos, (Nat.cast_nonneg m : (0 : ℝ) ≤ (m : ℝ))]

/-- **The derived coin cost of the Monte-Carlo estimator is exactly its sample count**, on
any body whose measurable hull contains a point and misses another (in unit-ball
coordinates).  Not an upper bound, not a convention: an equality. -/
theorem coinCost_est_eq {K : Set (Space n)} (ε pf : ℝ) {xh xm : Space n}
    (hh : xh ∈ MonteCarlo.target K) (hm : xm ∉ MonteCarlo.target K) :
    coinCost (MonteCarlo.est K ε pf) = (MonteCarlo.nSamp K ε pf : ℕ∞) := by
  refine le_antisymm (coinCost_le (readsAtMost_est K ε pf)) ?_
  have h := succ_le_coinCost (not_readsAtMost_est (K := K) ε pf hh hm)
  have hsucc : MonteCarlo.nSamp K ε pf - 1 + 1 = MonteCarlo.nSamp K ε pf :=
    Nat.succ_pred_eq_of_pos (MonteCarlo.nSamp_pos K ε pf)
  rwa [hsucc] at h

/-- **A body on which the cost is exactly `nSamp`.**  The unit ball in dimension `n ≥ 1`:
the origin is a hit, and `Ttc.MonteCarlo.exists_notMem_hull_unitBall` — the same witness the
anti-cheat `Ttc.MonteCarlo.est_ne_volume` uses — supplies a miss.  So the notion is not
vacuously satisfied and `Ttc.MonteCarlo.nSamp` really is the number of coins consumed. -/
theorem coinCost_est_unitBall (hn : n ≠ 0) (ε pf : ℝ) :
    coinCost (MonteCarlo.est (Metric.ball (0 : Space n) 1) ε pf)
      = (MonteCarlo.nSamp (Metric.ball (0 : Space n) 1) ε pf : ℕ∞) := by
  obtain ⟨v, hv⟩ := MonteCarlo.exists_notMem_hull_unitBall hn
  refine coinCost_est_eq (K := Metric.ball (0 : Space n) 1) ε pf
    (xh := 0) (xm := (MonteCarlo.rad (Metric.ball (0 : Space n) 1))⁻¹ • v) ?_ ?_
  · rw [MonteCarlo.target, Set.mem_preimage, smul_zero]
    exact subset_toMeasurable _ _ (Metric.mem_ball_self one_pos)
  · rw [MonteCarlo.target, Set.mem_preimage]
    simpa [smul_inv_smul₀ (MonteCarlo.rad_ne_zero (Metric.ball (0 : Space n) 1))] using hv

/-! ## The constructed `Vol_ED`, and the run's own oracle bundle

`Ttc.mcVolCoins` and `Ttc.ttcVolCoins` (`Exec/Complexity` §4) were introduced there as a
*pricing convention* on the grounds that no cost model existed.  One does now, and the two
lemmas below say what those numbers are with respect to it: upper bounds on the derived
cost.  Nothing about them is weakened — they are still not running times — but they are no
longer arbitrary. -/

variable {A : Type*}

/-- The constructed `Vol_ED` at cube `i` reads at most `Ttc.mcVolCoins` coins.  This is
`Ttc.mcVol_congr_of_agree` read as a statement in the cost model. -/
theorem readsAtMost_mcVol (M : A → Set (Space n)) (D : DNF A)
    (cen : {c : Cube A // c ∈ D} → Space n) (γ ε' δ' : ℝ) (i : Cube A) :
    ReadsAtMost (fun c => mcVol M D cen γ ε' δ' c i) (mcVolCoins M D cen γ ε' δ' i) :=
  fun _ _ h => mcVol_congr_of_agree M D cen γ ε' δ' i h

/-- **`Ttc.mcVolCoins` dominates the derived coin cost of the constructed `Vol_ED`.** -/
theorem coinCost_mcVol_le (M : A → Set (Space n)) (D : DNF A)
    (cen : {c : Cube A // c ∈ D} → Space n) (γ ε' δ' : ℝ) (i : Cube A) :
    coinCost (fun c => mcVol M D cen γ ε' δ' c i)
      ≤ ((mcVolCoins M D cen γ ε' δ' i : ℕ) : ℕ∞) :=
  coinCost_le (readsAtMost_mcVol M D cen γ ε' δ' i)

/-- **`Ttc.ttcVolCoins` dominates the derived coin cost of the `vol` field of the run's own
oracle bundle.**  This is the sense in which `cVol` now denotes something: at cube `i` it
denotes `Ttc.coinCost (fun c => (ttcOracleBundle … c t).vol i)`, and the price
`Exec/Complexity` §4 charges is an upper bound for it. -/
theorem coinCost_ttcVol_le (atoms : A → LinAtom n) (φ : BForm A) (ε δ : ℝ)
    (t : ℕ → Fin (ttcIndex atoms φ ε δ) → ℕ) (i : Cube A) :
    coinCost (fun c => (ttcOracleBundle atoms φ ε δ c t).vol i)
      ≤ ((ttcVolCoins atoms φ ε δ i : ℕ) : ℕ∞) :=
  coinCost_le fun c c' h => ttcOracleBundle_vol_congr atoms φ ε δ c c' t i h

end Volume

/-! # §3  The sampler's chain: the step-budget cost, derived

`Ttc.ballWalkLaw K δ mu0 t` is *defined* as the `t`-th iterate of a kernel, so "it takes
`t` steps" is true by `rfl` and says nothing.  What is not definitional, and is the only
thing a mixing theorem can be attached to, is the least budget at which the law meets its
accuracy specification.  That is `Ttc.mixCost`. -/

section Sampler

variable {n : ℕ}

/-- **The budget is a budget.**  Running `s + t` steps is running `s` and resuming for `t`
from the law reached.  Without this, a "step count" would be an uninterpreted numeral; with
it, budgets compose, which is the minimum an operational reading requires. -/
theorem ballWalkLaw_add (K : Set (Space n)) (dl : ℝ) (mu0 : Measure (Space n)) (s t : ℕ) :
    ballWalkLaw K dl mu0 (s + t) = ballWalkLaw K dl (ballWalkLaw K dl mu0 s) t :=
  Arlib.MarkovChains.iterate_add _ _ s t

/-- **The step cost of the lazy ball walk**: the least number of steps at which the law
started from `mu0` is within `eps` of `π` in total variation, and `⊤` if no budget
achieves it.

This is *not* the assertion that the sampler takes this many steps — it is the least budget
at which the constructed law satisfies its own specification, derived from
`Ttc.ballWalkLaw`'s definition and the target.  A mixing-time theorem is exactly an upper
bound on it (`Ttc.mixCost_le_mixSteps`). -/
noncomputable def mixCost (K : Set (Space n)) (dl : ℝ) (mu0 pi : Measure (Space n))
    (eps : ℝ≥0∞) : ℕ∞ :=
  ⨅ t : {t : ℕ // Arlib.TVLe (ballWalkLaw K dl mu0 t) pi eps}, (t.1 : ℕ∞)

/-- Any budget that meets the specification bounds the cost. -/
theorem mixCost_le {K : Set (Space n)} {dl : ℝ} {mu0 pi : Measure (Space n)} {eps : ℝ≥0∞}
    {t : ℕ} (h : Arlib.TVLe (ballWalkLaw K dl mu0 t) pi eps) :
    mixCost K dl mu0 pi eps ≤ (t : ℕ∞) :=
  iInf_le (fun t : {t : ℕ // Arlib.TVLe (ballWalkLaw K dl mu0 t) pi eps} => (t.1 : ℕ∞))
    ⟨t, h⟩

/-- Lower bounds come from lower bounds on every achieving budget. -/
theorem le_mixCost {K : Set (Space n)} {dl : ℝ} {mu0 pi : Measure (Space n)} {eps : ℝ≥0∞}
    {m : ℕ∞} (h : ∀ t, Arlib.TVLe (ballWalkLaw K dl mu0 t) pi eps → m ≤ (t : ℕ∞)) :
    m ≤ mixCost K dl mu0 pi eps := le_iInf fun t => h t.1 t.2

/-- A looser tolerance costs no more. -/
theorem mixCost_mono {K : Set (Space n)} {dl : ℝ} {mu0 pi : Measure (Space n)}
    {eps eps' : ℝ≥0∞} (h : eps ≤ eps') :
    mixCost K dl mu0 pi eps' ≤ mixCost K dl mu0 pi eps :=
  le_mixCost fun _ ht => mixCost_le (ht.mono h)

/-- **At least one step is needed** when the start does not already meet the
specification. -/
theorem one_le_mixCost {K : Set (Space n)} {dl : ℝ} {mu0 pi : Measure (Space n)} {eps : ℝ≥0∞}
    (h : ¬ Arlib.TVLe mu0 pi eps) : 1 ≤ mixCost K dl mu0 pi eps := by
  refine le_mixCost fun t ht => ?_
  rcases Nat.eq_zero_or_pos t with h0 | hpos
  · rw [h0, ballWalkLaw_zero] at ht
    exact absurd ht h
  · exact_mod_cast hpos

/-- **`Ttc.mixCost` is not identically zero.**  From a point mass at `x` to a point mass at
some `y ≠ x`, at tolerance `0`, the cost is at least one step.  Without a witness like this
the notion could be satisfied by `0` everywhere and would measure nothing. -/
theorem one_le_mixCost_dirac (K : Set (Space n)) (dl : ℝ) {x y : Space n} (hxy : x ≠ y) :
    1 ≤ mixCost K dl (Measure.dirac x) (Measure.dirac y) 0 := by
  refine one_le_mixCost fun h => ?_
  have heq : (Measure.dirac x : Measure (Space n)) = Measure.dirac y := h.eq_of_zero
  have h1 : (Measure.dirac x : Measure (Space n)) {x} = 1 :=
    Measure.dirac_apply_of_mem (Set.mem_singleton x)
  have h2 : (Measure.dirac y : Measure (Space n)) {x} = 0 := by
    rw [Measure.dirac_apply' _ (measurableSet_singleton x), Set.indicator_of_notMem]
    exact fun hc => hxy (Set.mem_singleton_iff.1 hc).symm
  rw [heq, h2] at h1
  exact absurd h1 (by simp)

/-! ## The proved instance: `Ttc.mixSteps` bounds the derived cost

`Ttc.tvLe_ballWalkLaw_inflated` (`Sampler/Construct`) says the `Ttc.mixSteps`-step law of
the lazy ball walk on the Kannan–Vempala inflated polytope is within `eps` of uniform on
it.  Read in this cost model, that is an upper bound on `Ttc.mixCost` — and it is the only
form in which a mixing theorem can price a subroutine. -/

/-- **The derived step cost is at most `Ttc.mixSteps`.**  Hypotheses are exactly those of
`Ttc.tvLe_ballWalkLaw_inflated`: a diameter bound, an inscribed ball, a step at most the
inradius, and a warm start.  Nothing about the sampler's accuracy is assumed. -/
theorem mixCost_le_mixSteps {ι : Type*} (hn : 1 ≤ n)
    (Am : ι → Space n) (bv : ι → ℝ) (cc r : ℝ) {Dm : ℝ}
    (hD : ∀ x ∈ Arlib.KV97.inflated Am bv cc r, ∀ y ∈ Arlib.KV97.inflated Am bv cc r,
      dist x y ≤ Dm)
    {cen : Space n} {γ : ℝ} (hγ : 0 < γ)
    (hball : Metric.ball cen γ ⊆ Arlib.KV97.inflated Am bv cc r)
    {dl : ℝ} (hδ : 0 < dl) (hδγ : dl ≤ γ)
    {mu0 : Measure (Space n)} [IsProbabilityMeasure mu0] {Mw : ℝ} (hMw : 1 ≤ Mw)
    (hwarm : Arlib.IsWarm (ENNReal.ofReal Mw) mu0
      (Arlib.uniformOn volume (Arlib.KV97.inflated Am bv cc r)))
    {eps : ℝ} (heps : 0 < eps) :
    mixCost (Arlib.KV97.inflated Am bv cc r) dl mu0
        (Arlib.uniformOn volume (Arlib.KV97.inflated Am bv cc r)) (ENNReal.ofReal eps)
      ≤ ((mixSteps n γ Dm dl Mw eps : ℕ) : ℕ∞) :=
  mixCost_le (tvLe_ballWalkLaw_inflated hn Am bv cc r hD hγ hball hδ hδγ hMw hwarm heps)

/-- **The same at the arguments the constructed sampler supplies.**
`Ttc.e2eSampD_eq_ballWalk` (`Exec/Complexity` §4) proves, by `rfl`, that `Ttc.e2eSampD` is
`Ttc.kv97SampD` of the ball walk run for `Ttc.e2eBallWalkSteps` steps.  This says that
budget meets the specification, so it dominates the derived cost.

This is the attachment point for a KV97 / Hit-and-Run mixing result: such a theorem would
replace `Ttc.e2eBallWalkSteps` on the right by a smaller number, and nothing else in this
file would change. -/
theorem mixCost_le_e2eBallWalkSteps {A : Type*} {D : DNF A} (hn : 1 ≤ n) (ρ : ℤ)
    (epsPrime rfac : ℝ) {Jt : Type}
    (Am : {c : Cube A // c ∈ D} → Jt → Space n) (bv : {c : Cube A // c ∈ D} → Jt → ℝ)
    (cen : {c : Cube A // c ∈ D} → Space n) (gammaHat : ℝ)
    (Dm : {c : Cube A // c ∈ D} → ℝ) (i : {c : Cube A // c ∈ D})
    (hD : ∀ x ∈ Arlib.KV97.inflated (Am i) (bv i) (Arlib.KV97.cOf epsPrime) rfac,
      ∀ y ∈ Arlib.KV97.inflated (Am i) (bv i) (Arlib.KV97.cOf epsPrime) rfac,
      dist x y ≤ (1 + Arlib.KV97.kappaOf (Arlib.KV97.cOf epsPrime) rfac /
        (latticeScale ρ * gammaHat)) * Dm i)
    (hγ : 0 < latticeScale ρ * gammaHat
      + Arlib.KV97.kappaOf (Arlib.KV97.cOf epsPrime) rfac)
    (hball : Metric.ball (latticeScale ρ • cen i)
        (latticeScale ρ * gammaHat + Arlib.KV97.kappaOf (Arlib.KV97.cOf epsPrime) rfac)
      ⊆ Arlib.KV97.inflated (Am i) (bv i) (Arlib.KV97.cOf epsPrime) rfac)
    (hδ : 0 < latticeScale ρ * gammaHat)
    (hδγ : latticeScale ρ * gammaHat ≤ latticeScale ρ * gammaHat
      + Arlib.KV97.kappaOf (Arlib.KV97.cOf epsPrime) rfac)
    (hMw : (1 : ℝ) ≤ (volume (Arlib.KV97.inflated (Am i) (bv i)
        (Arlib.KV97.cOf epsPrime) rfac) /
      volume (Metric.ball (latticeScale ρ • cen i)
        (latticeScale ρ * gammaHat
          + Arlib.KV97.kappaOf (Arlib.KV97.cOf epsPrime) rfac))).toReal)
    (hwarm : Arlib.IsWarm (ENNReal.ofReal
        ((volume (Arlib.KV97.inflated (Am i) (bv i) (Arlib.KV97.cOf epsPrime) rfac) /
          volume (Metric.ball (latticeScale ρ • cen i)
            (latticeScale ρ * gammaHat
              + Arlib.KV97.kappaOf (Arlib.KV97.cOf epsPrime) rfac))).toReal))
        (Arlib.uniformOn volume (Metric.ball (latticeScale ρ • cen i)
          (latticeScale ρ * gammaHat
            + Arlib.KV97.kappaOf (Arlib.KV97.cOf epsPrime) rfac)))
        (Arlib.uniformOn volume
          (Arlib.KV97.inflated (Am i) (bv i) (Arlib.KV97.cOf epsPrime) rfac)))
    (heps : 0 < epsPrime / (4 *
      (volume (Arlib.KV97.inflated (Am i) (bv i) (Arlib.KV97.cOf epsPrime) rfac)).toReal)) :
    mixCost (Arlib.KV97.inflated (Am i) (bv i) (Arlib.KV97.cOf epsPrime) rfac)
        (latticeScale ρ * gammaHat)
        (Arlib.uniformOn volume (Metric.ball (latticeScale ρ • cen i)
          (latticeScale ρ * gammaHat
            + Arlib.KV97.kappaOf (Arlib.KV97.cOf epsPrime) rfac)))
        (Arlib.uniformOn volume
          (Arlib.KV97.inflated (Am i) (bv i) (Arlib.KV97.cOf epsPrime) rfac))
        (ENNReal.ofReal (epsPrime / (4 *
          (volume (Arlib.KV97.inflated (Am i) (bv i)
            (Arlib.KV97.cOf epsPrime) rfac)).toReal)))
      ≤ ((e2eBallWalkSteps ρ epsPrime rfac Am bv cen gammaHat Dm i : ℕ) : ℕ∞) := by
  haveI : IsProbabilityMeasure (Arlib.uniformOn volume (Metric.ball
      (latticeScale ρ • cen i) (latticeScale ρ * gammaHat
        + Arlib.KV97.kappaOf (Arlib.KV97.cOf epsPrime) rfac))) :=
    Arlib.isProbabilityMeasure_uniformOn volume
      (Metric.measure_ball_pos volume _ hγ).ne' measure_ball_lt_top.ne
  exact mixCost_le_mixSteps hn (Am i) (bv i) (Arlib.KV97.cOf epsPrime) rfac hD hγ hball
    hδ hδγ hMw hwarm heps

end Sampler

/-! # §4  What the model says about the rejection rounds — and what it cannot

`Ttc.kv97SampD` is a *density*, not a function of coins and not a budgeted family of
measures, so neither §1 nor §3 applies to it: there is no object in this development that
performs the rejection loop, hence nothing whose cost could be derived.  That is a fact
about what has been constructed, not a limitation of the model, and it is the reason
`Exec/Complexity` §4's charge undercounts.

What the model *can* say is what shape the missing cost has.  `Ttc.firstAccept` below is
the round count of a rejection loop — the index of the first accepting coin — written as an
honest function of a coin sequence, and its cost is `⊤`: no finite prefix determines it.
The theorem is about `Ttc.firstAccept`, which is defined here; it is **not** a theorem
about `Ttc.kv97SampD`, and must not be quoted as one. -/

section Rejection

/-- **A model rejection loop's round count**: the index of the first accepting coin.  Not
part of `TTC`; defined here so that §1's `⊤` value has a witness and so that the shape of
the sampler's uncounted work is on record. -/
noncomputable def firstAccept (c : ℕ → Bool) : ℕ := sInf {i | c i = true}

/-- On a sequence accepting only at `k`, the loop runs `k` rounds. -/
theorem firstAccept_single (k : ℕ) : firstAccept (fun i => decide (i = k)) = k := by
  have hset : {i | (decide (i = k) : Bool) = true} = {k} := by ext i; simp
  rw [firstAccept, hset]
  exact csInf_singleton k

/-- **No finite prefix of the coins determines the round count.**  Two sequences that both
reject everywhere below `k` can accept first at `k` or at `k + 1`. -/
theorem not_readsAtMost_firstAccept (k : ℕ) : ¬ ReadsAtMost firstAccept k := by
  intro h
  have hagree : ∀ j < k, (fun i => decide (i = k)) j = (fun i => decide (i = k + 1)) j := by
    intro j hj
    simp only [decide_eq_decide]
    omega
  have := h _ _ hagree
  rw [firstAccept_single k, firstAccept_single (k + 1)] at this
  omega

/-- **The rejection loop's cost is `⊤`.**  The cost model can express "unboundedly many
coins", and does so exactly where a worst-case round count fails to exist.  This is the
statement that has no counterpart at `Ttc.kv97SampD`, because `Ttc.kv97SampD` consumes no
coins at all. -/
theorem coinCost_firstAccept : coinCost firstAccept = ⊤ :=
  coinCost_eq_top not_readsAtMost_firstAccept

end Rejection

end Ttc

/-! ## Axiom profile -/

#print axioms Ttc.ReadsAtMost
#print axioms Ttc.ReadsAtMost.mono
#print axioms Ttc.readsAtMost_const
#print axioms Ttc.readsAtMost_eval
#print axioms Ttc.ReadsAtMost.map
#print axioms Ttc.ReadsAtMost.comp₂
#print axioms Ttc.ReadsAtMost.finsetSum
#print axioms Ttc.ReadsAtMost.dite
#print axioms Ttc.coinCost
#print axioms Ttc.coinCost_le
#print axioms Ttc.le_coinCost
#print axioms Ttc.succ_le_coinCost
#print axioms Ttc.coinCost_eq_succ
#print axioms Ttc.coinCost_eq_top

#print axioms Ttc.readsAtMost_score
#print axioms Ttc.readsAtMost_est
#print axioms Ttc.not_readsAtMost_est
#print axioms Ttc.coinCost_est_eq
#print axioms Ttc.coinCost_est_unitBall
#print axioms Ttc.readsAtMost_mcVol
#print axioms Ttc.coinCost_mcVol_le
#print axioms Ttc.coinCost_ttcVol_le

#print axioms Ttc.ballWalkLaw_add
#print axioms Ttc.mixCost
#print axioms Ttc.mixCost_le
#print axioms Ttc.le_mixCost
#print axioms Ttc.mixCost_mono
#print axioms Ttc.one_le_mixCost
#print axioms Ttc.one_le_mixCost_dirac
#print axioms Ttc.mixCost_le_mixSteps
#print axioms Ttc.mixCost_le_e2eBallWalkSteps

#print axioms Ttc.firstAccept
#print axioms Ttc.firstAccept_single
#print axioms Ttc.not_readsAtMost_firstAccept
#print axioms Ttc.coinCost_firstAccept

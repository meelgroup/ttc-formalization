/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import Ttc.Monadic.MeasurePr
import Ttc.Monadic.Pair

/-!
# `Monadic/Program`: `TTC`'s run, as one law on one space

`Ttc.ttc_accuracy_single_measure` (`Monadic/EventMeasurable`) states the accuracy
guarantee over the composition–product

```
MonteCarlo.coins n ⊗ₘ ttcTrajKernel …
```

— the volume oracle's coins, then the trajectory law at the rates *that* draw
produced.  This file gives that measure a name, `Ttc.ttcLaw`, so that the headline
`Ttc.ttc_volume_estimate` can state **both** of its conjuncts about a single point
`p = (c, t)` of a single space, drawn from a single law: no iterated integral, and
no pair of separately-quantified coin sequences.

`Ttc.ttcLaw` is the analogue of nfalean's `ApproxNFA.countNFAM`, with one honest
difference recorded in `Monadic/MeasurePr`'s docstring and repeated here: ours is a
`MeasureTheory.Measure`, not a `PMF`.  `Ttc.MonteCarlo.coins` is
`MeasureTheory.Measure.infinitePi` of the uniform law on a Euclidean ball — atomless
on an uncountable space — so there is no `PMF` whose `toOuterMeasure` it is, and the
`PMF` monad is simply unavailable.  What survives is the Giry-monad structure:
`Ttc.ttcTrajKernel` is a genuine Markov kernel (`Monadic/Kernel`), so `⊗ₘ` is the
monadic bind of a probability measure with it, and `Ttc.ttcLaw` is again a
probability measure (`Ttc.instIsProbabilityMeasureTtcLaw`).

Three declarations, no proof content: `Ttc.ttcLaw`, its `rfl` lemma
`Ttc.ttcLaw_def`, and the `IsProbabilityMeasure` instance.

## The paired law `Ttc.ttcPairLaw`

The second half of this file is the closest available analogue of nfalean's

```
countNFAM A n ε δ : PMF (ℝ × ℕ)
```

— a single object returning `(estimate, cost)`, so that both halves of a headline can
be read off *one* draw.  Ours is `Ttc.ttcLaw` pushed forward along the deterministic
read-off `Ttc.ttcPair`,

```
p ↦ (ttcRun … p.1 p.2, ttcCost … p.1 p.2 cVol cSample) : ℝ × ℕ
```

giving `Ttc.ttcPairLaw … cVol cSample : Measure (ℝ × ℕ)`, again a probability measure
(`Ttc.instIsProbabilityMeasureTtcPairLaw`).  Both components are countably determined
in the run — the output by `Ttc.countablyDetermined_ttcAlgOutput_joint`, the cost by
`Ttc.countablyDetermined_ttcCost_joint` (`Monadic/Pair`) — so the read-off is
measurable and the pushforward is honest.

### Why the two per-call charges stay as parameters

`Ttc.ttcCost … c t cVol cSample` takes the cost of one `Vol_ED` call and the cost of
one generated sample as arguments, because `Runtime.lean` cannot derive them: `Vol_ED`
and `GenerateSamples` are *oracles*, and the model fixes what they return, never how
they compute it.  The headline's runtime conjunct is therefore universally quantified
over `cVol` and `cSample`.  `Ttc.ttcPairLaw` keeps them as **parameters of the law**
rather than fixing them (to `1`, say): fixing them would silently replace a statement
about every charging convention by a statement about one, and there is no distinguished
convention to pick.  So there is one pair law per charging convention, and every
statement below is quantified over `cVol` and `cSample` exactly as the headline is.

### What transfers, and what does not

`Ttc.PrR_ttcPairLaw` transfers **every** event, with no measurability hypothesis at
all — `Ttc.map_apply_of_countablyDetermined` (`Monadic/Pair`) supplies what nfalean gets
for free from `PMF.toOuterMeasure`.  `Ttc.ttc_accuracy_pairLaw` is the headline's
accuracy conjunct restated over the pair law, with nothing lost.

The runtime conjunct does **not** move across intact, and this file does not pretend
otherwise.  Two obstructions, both real:

* the bound is guarded by `Ttc.ttcTerminates … p.1 p.2`, which is a property of the
  *run* `p` and is not a function of the pair `(estimate, cost)`.  So the faithful
  statement over the pair law is about the image of the terminating set,
  `Ttc.ttcPairLaw_cost_le`, and the guard survives as that image;
* "every run the program can produce" is `Set.range (Ttc.ttcPair …)` — the image of
  the *whole* run space.  That is `Ttc.ttcPairLaw_cost_le_of_terminates`, the
  headline-facing form, and it is the honest analogue of nfalean's `All[r ← …]`.

**The collapse, which is the opposite of the discrete intuition.**  One might expect a
support-based quantifier to be stronger than `∀ᵐ`, as `PMF.support ⊆ {x | E x}` is often
described.  For `Ttc.ttcPairLaw` it is **not**: `Ttc.all_ttcPairLaw_iff_atoms` proves that
`∀ᵐ` is *equivalent* to the literal `PMF`-support reading "`E` holds at every outcome of
positive mass".  The reason is structural — the pair law is a pushforward along a
**countably determined** read-off, so it is carried by the countable
`Set.range (Ttc.ttcPair …)`, and a countable carrier leaves no room for a large-but-null
exceptional set inside the range.  (That named hypothesis is where the collapse lives:
`Ttc.ae_map_iff_atoms_of_countablyDetermined` in `Monadic/Pair` states it in general, and
without it the equivalence is false.)

So dressing the runtime conjunct in a support-based quantifier buys **nothing** over
`All[…]`, and both are strictly weaker than `Ttc.ttcPairLaw_cost_le_of_terminates`:
`Ttc.all_ttcPairLaw_cost_le` derives the a.e. form from the range form, one way only.
`Model/Theorem.lean`'s runtime conjunct therefore stays pointwise over runs.
-/

namespace Ttc

open MeasureTheory ProbabilityTheory
open Ttc.Monadic

section Law

variable {A : Type*} {n : ℕ} (atoms : A → LinAtom n) (φ : BForm A) (ε δ : ℝ)
    (hε0 : 0 < ε) (hε1 : ε ≤ 1) (hn : 1 ≤ n) (hφ : φ.IsPositive)
    (hpos : 0 < volSol (atomSet atoms) φ)

/-- **The law of one run of `TTC(F, ε, δ)`**: a measure on pairs
`p = (volume coins, sample trajectory)`.

The composition–product of the volume oracle's coin law `Ttc.MonteCarlo.coins` with
the coin-indexed trajectory kernel `Ttc.ttcTrajKernel` — that is, draw the volume
coins `c`, then draw the trajectory from the coupled family at the rates `c`
produced.  Everything the algorithm reads on a run is a function of `p`: the oracle
bundle is `Ttc.ttcOracleBundle … p.1 p.2`, the output is
`Ttc.ttcAlgOutput … (that bundle)`, and the charged cost is `Ttc.ttcCost … p.1 p.2`.

This is what makes `Ttc.ttc_volume_estimate`'s two conjuncts statements about *the
same run*, and it is why that theorem has no iterated integral. -/
noncomputable def ttcLaw :
    Measure ((ℕ → Space n) × (ℕ → Fin (ttcIndex atoms φ ε δ) → ℕ)) :=
  MonteCarlo.coins n ⊗ₘ ttcTrajKernel atoms φ ε δ

/-- **What `Ttc.ttcLaw` is**, by `rfl`: the composition–product of the volume coins
with the coin-indexed trajectory kernel.  This is the identification that lets
`Ttc.ttc_accuracy_single_measure` be quoted verbatim as the headline's accuracy
conjunct. -/
theorem ttcLaw_def :
    ttcLaw atoms φ ε δ
      = MonteCarlo.coins n ⊗ₘ ttcTrajKernel atoms φ ε δ := rfl

/-- **A run's law is a probability measure.**  `Ttc.MonteCarlo.coins` is one
(`Ttc.MonteCarlo.instIsProbabilityMeasureCoins`) and `Ttc.ttcTrajKernel` is Markov
(`Ttc.isMarkovKernel_ttcTrajKernel`), so Mathlib's instance for `⊗ₘ` applies. -/
instance instIsProbabilityMeasureTtcLaw :
    IsProbabilityMeasure (ttcLaw atoms φ ε δ) := by
  rw [ttcLaw_def]
  infer_instance

/-! ## The paired law: one measure on `(estimate, cost)` -/

/-- **The deterministic read-off `p ↦ (estimate, cost)`.**

`Ttc.ttcRun` is `Model/Pseudocode`'s own output on the run `p = (c, t)` — the oracle
bundle filled in from `p` itself — and `Ttc.ttcCost` is `alg:ttc`'s charged cost on the
same run, at the per-call charges `cVol` (one `Vol_ED` call) and `cSample` (one
generated sample).  No randomness: this is a function of the run. -/
noncomputable def ttcPair (cVol cSample : ℕ) :
    (ℕ → Space n) × (ℕ → Fin (ttcIndex atoms φ ε δ) → ℕ) → ℝ × ℕ :=
  fun p =>
    (ttcRun atoms φ ε δ p.1 p.2,
      ttcCost atoms φ ε δ p.1 p.2 cVol cSample)

/-- **What `Ttc.ttcPair` is**, by `rfl`. -/
theorem ttcPair_def (cVol cSample : ℕ)
    (p : (ℕ → Space n) × (ℕ → Fin (ttcIndex atoms φ ε δ) → ℕ)) :
    ttcPair atoms φ ε δ cVol cSample p
      = (ttcRun atoms φ ε δ p.1 p.2,
          ttcCost atoms φ ε δ p.1 p.2 cVol cSample) := rfl

/-- **The read-off is countably determined**: its first component by
`Ttc.countablyDetermined_ttcAlgOutput_joint` (`Ttc.ttcRun` is that term, by `rfl`), its
second by `Ttc.countablyDetermined_ttcCost_joint` (`Monadic/Pair`). -/
theorem countablyDetermined_ttcPair (cVol cSample : ℕ) :
    CountablyDetermined (ttcPair atoms φ ε δ cVol cSample) :=
  (countablyDetermined_ttcAlgOutput_joint atoms φ ε δ).prodMk
    (countablyDetermined_ttcCost_joint atoms φ ε δ cVol cSample)

/-- **The read-off is measurable.** -/
theorem measurable_ttcPair (cVol cSample : ℕ) :
    Measurable (ttcPair atoms φ ε δ cVol cSample) :=
  (countablyDetermined_ttcPair atoms φ ε δ cVol cSample).measurable

/-- **The law of `(estimate, cost)` on one run of `TTC(F, ε, δ)`** — `Ttc.ttcLaw` pushed
forward along `Ttc.ttcPair`.  This is the `Measure` analogue of nfalean's
`ApproxNFA.countNFAM : PMF (ℝ × ℕ)`; see the module docstring for why the two per-call
charges stay parameters and for what does and does not transfer to it. -/
noncomputable def ttcPairLaw (cVol cSample : ℕ) : Measure (ℝ × ℕ) :=
  (ttcLaw atoms φ ε δ).map
    (ttcPair atoms φ ε δ cVol cSample)

/-- **What `Ttc.ttcPairLaw` is**, by `rfl`. -/
theorem ttcPairLaw_def (cVol cSample : ℕ) :
    ttcPairLaw atoms φ ε δ cVol cSample
      = (ttcLaw atoms φ ε δ).map
          (ttcPair atoms φ ε δ cVol cSample) := rfl

/-- **The paired law is a probability measure**, from `Ttc.instIsProbabilityMeasureTtcLaw`
and the measurability of the read-off. -/
instance instIsProbabilityMeasureTtcPairLaw (cVol cSample : ℕ) :
    IsProbabilityMeasure (ttcPairLaw atoms φ ε δ cVol cSample) := by
  rw [ttcPairLaw_def]
  exact Measure.isProbabilityMeasure_map
    (measurable_ttcPair atoms φ ε δ cVol cSample).aemeasurable

/-! ### Transfer

The pair law's mass at **any** set is the run law's mass at its preimage — no
measurability hypothesis, because `Ttc.ttcPair` has countable range
(`Ttc.map_apply_of_countablyDetermined`, `Monadic/Pair`).  This is what nfalean gets for
free from `PMF.toOuterMeasure`, whose Carathéodory σ-algebra is `⊤`. -/

/-- **The pair law at an arbitrary set** is the run law at its preimage. -/
theorem ttcPairLaw_apply (cVol cSample : ℕ) (S : Set (ℝ × ℕ)) :
    ttcPairLaw atoms φ ε δ cVol cSample S
      = ttcLaw atoms φ ε δ
          (ttcPair atoms φ ε δ cVol cSample ⁻¹' S) :=
  map_apply_of_countablyDetermined
    (countablyDetermined_ttcPair atoms φ ε δ cVol cSample) _ S

/-- **`Pr` transfers across the read-off, for every event.**  The `Measure`-level
counterpart of nfalean's `PMF.PrR_map`, and like it it needs no hypotheses. -/
theorem PrR_ttcPairLaw (cVol cSample : ℕ) (E : ℝ × ℕ → Prop) :
    Pr[r ← ttcPairLaw atoms φ ε δ cVol cSample; E r]
      = Pr[p ← ttcLaw atoms φ ε δ;
          E (ttcPair atoms φ ε δ cVol cSample p)] :=
  congrArg ENNReal.toReal
    (ttcPairLaw_apply atoms φ ε δ cVol cSample {r | E r})

/-- **The accuracy transfer.**  An event about the pair's *estimate* component is the
same event about `Model/Pseudocode`'s `Ttc.ttcRun` on the underlying run — so nothing is
lost by stating the accuracy conjunct over `Ttc.ttcPairLaw`. -/
theorem PrR_ttcPairLaw_fst (cVol cSample : ℕ) (S : Set ℝ) :
    Pr[r ← ttcPairLaw atoms φ ε δ cVol cSample; r.1 ∈ S]
      = Pr[p ← ttcLaw atoms φ ε δ;
          ttcRun atoms φ ε δ p.1 p.2 ∈ S] :=
  PrR_ttcPairLaw atoms φ ε δ cVol cSample fun r => r.1 ∈ S

include hε0 hε1 hn hφ hpos in
/-- **The headline's accuracy conjunct over the paired law.**  `Ttc.ttc_volume_estimate`'s
first half, verbatim, with the run law replaced by the law of `(estimate, cost)`: the
estimate component lands in `(1 ± ε)·Vol(F)` with probability at least `1 − δ`.  Nothing
is weakened — `Ttc.PrR_ttcPairLaw_fst` is an equality. -/
theorem ttc_accuracy_pairLaw (hδ0 : 0 < δ) (hδ1 : δ ≤ 1) (cVol cSample : ℕ) :
    1 - δ ≤ Pr[r ← ttcPairLaw atoms φ ε δ cVol cSample;
      r.1 ∈ relErr ε (volSol (atomSet atoms) φ)] := by
  rw [PrR_ttcPairLaw_fst]
  exact ttc_accuracy_single_measure atoms φ ε δ hε0 hε1 hn hφ hpos hδ0 hδ1

/-! ### The runtime half, and what it costs to move it

`Ttc.ttcTerminates` is a property of the *run*, not of the pair, so the faithful
statement over the pair law is about the image of the terminating set.  Under a global
termination hypothesis that image becomes all of `Set.range (Ttc.ttcPair …)` — "every
outcome the program can produce", which is what nfalean's `All[r ← …]` means for a
`PMF`.  The a.e. form is derived from it, and is strictly weaker. -/

include hε0 hε1 hn hφ hpos in
/-- **The runtime conjunct over the paired law**, faithfully: every pair produced by a
*terminating* run has cost at most `m · (C_vol + C_sample · (Thresh + 1))`.

The bound is `Ttc.ttcCost_le_thresh_add_one` (`Exec/Api`) — the real-arithmetic form,
with no integrality side condition relating a natural `thr` to the real `Ttc.ttcThresh`.
The `Ttc.ttcTerminates` guard survives as the set the image is taken over; it cannot
survive as a condition on `r`, because termination is a property of the *run* and is not
a function of the pair `(estimate, cost)`. -/
theorem ttcPairLaw_cost_le (hδ0 : 0 < δ) (hδ1 : δ ≤ 1) (cVol cSample : ℕ) :
    ∀ r ∈ ttcPair atoms φ ε δ cVol cSample ''
        {p | ttcTerminates atoms φ ε δ p.1 p.2},
      (r.2 : ℝ) ≤ (ttcNumCubes atoms φ : ℝ)
        * ((cVol : ℝ) + (cSample : ℝ)
            * (ttcThresh atoms φ ε δ + 1)) := by
  rintro r ⟨p, hp, rfl⟩
  exact ttcCost_le_thresh_add_one atoms φ ε δ hε0 hε1 hn hφ hpos hδ0 hδ1 p.1 p.2
    cVol cSample hp

include hε0 hε1 hn hφ hpos in
/-- **Every outcome the program can produce meets the bound**, under global termination.

This is the headline-facing form of the runtime half over the paired law, and it is
**strictly stronger than both measure-theoretic quantifiers**:

* stronger than `All[…]` (`∀ᵐ`), which permits a null exceptional set —
  `Ttc.all_ttcPairLaw_cost_le` derives that form from this one;
* stronger than any support-based quantifier, because
  `Ttc.all_ttcPairLaw_iff_atoms` shows that for `Ttc.ttcPairLaw` the `PMF`-support notion
  ("`E` holds at every outcome of positive mass") is *equivalent* to `∀ᵐ`, hence also
  permits a null exceptional set.

`Set.range (Ttc.ttcPair …)` is literally "every outcome the program can produce": the
image of the *whole* run space, with no exceptional set, null or otherwise.  This is what
nfalean's `All[r ← countNFAM …; …]` means for a `PMF`, and it is why
`Model/Theorem.lean`'s runtime conjunct stays pointwise over runs. -/
theorem ttcPairLaw_cost_le_of_terminates (hδ0 : 0 < δ) (hδ1 : δ ≤ 1) (cVol cSample : ℕ)
    (hterm : ∀ p : (ℕ → Space n) × (ℕ → Fin (ttcIndex atoms φ ε δ) → ℕ),
      ttcTerminates atoms φ ε δ p.1 p.2) :
    ∀ r ∈ Set.range (ttcPair atoms φ ε δ cVol cSample),
      (r.2 : ℝ) ≤ (ttcNumCubes atoms φ : ℝ)
        * ((cVol : ℝ) + (cSample : ℝ)
            * (ttcThresh atoms φ ε δ + 1)) := by
  rintro r ⟨p, rfl⟩
  exact ttcCost_le_thresh_add_one atoms φ ε δ hε0 hε1 hn hφ hpos hδ0 hδ1 p.1 p.2
    cVol cSample (hterm p)

include hε0 hε1 hn hφ hpos in
/-- **The a.e. form, derived — and recorded as the weaker statement.**

`Ttc.ttcPairLaw_cost_le_of_terminates` is the theorem; this is all that survives of it if
one insists on writing the runtime conjunct with `Monadic/MeasurePr`'s `All[…]`.  It is a
corollary, never a replacement: `Model/Theorem.lean`'s runtime conjunct is pointwise over
runs precisely so that this weakening is not taken. -/
theorem all_ttcPairLaw_cost_le (hδ0 : 0 < δ) (hδ1 : δ ≤ 1) (cVol cSample : ℕ)
    (hterm : ∀ p : (ℕ → Space n) × (ℕ → Fin (ttcIndex atoms φ ε δ) → ℕ),
      ttcTerminates atoms φ ε δ p.1 p.2) :
    All[r ← ttcPairLaw atoms φ ε δ cVol cSample;
      (r.2 : ℝ) ≤ (ttcNumCubes atoms φ : ℝ)
        * ((cVol : ℝ) + (cSample : ℝ)
            * (ttcThresh atoms φ ε δ + 1))] := by
  refine MeasureTheory.ae_iff.2 ?_
  have hempty : ttcPair atoms φ ε δ cVol cSample ⁻¹'
      {r : ℝ × ℕ | ¬ ((r.2 : ℝ) ≤ (ttcNumCubes atoms φ : ℝ)
        * ((cVol : ℝ) + (cSample : ℝ)
            * (ttcThresh atoms φ ε δ + 1)))} = ∅ := by
    ext p
    simp only [Set.mem_preimage, Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, not_not]
    exact ttcPairLaw_cost_le_of_terminates atoms φ ε δ hε0 hε1 hn hφ hpos hδ0 hδ1
      cVol cSample hterm _ ⟨p, rfl⟩
  rw [ttcPairLaw_apply, hempty, measure_empty]

/-- **What the a.e. form is worth here: exactly the `PMF`-support notion — no more.**

`Ttc.ttcPairLaw` is the pushforward of a **countably determined** read-off
(`Ttc.countablyDetermined_ttcPair` — the named hypothesis of
`Ttc.ae_map_iff_atoms_of_countablyDetermined`, and the reason the collapse below holds).
So the law lives on the countable set `Set.range (Ttc.ttcPair …)`, and for such a law
"`E` holds at every outcome of positive mass" — the literal transcription of nfalean's
`PMF.support p ⊆ {x | E x}` — is *equivalent* to `∀ᵐ`, not stronger than it.

**This is the opposite of the discrete intuition**, and the difference is structural, not
incidental: a `PMF`'s support carries full mass by construction, so for nfalean the two
readings agree; here they agree for the same reason, because a countable carrier leaves no
room for a "large but null" exceptional set inside the range.  Consequently, dressing the
runtime conjunct in a support-based quantifier buys nothing over `All[…]`, and both are
strictly weaker than `Ttc.ttcPairLaw_cost_le_of_terminates`.  (`Monadic/MeasurePr`'s
`AllS[…]` is a *third*, topological, notion; its own separating examples show the three
are distinct in general — the collapse proved here is a fact about this law.) -/
theorem all_ttcPairLaw_iff_atoms (cVol cSample : ℕ) (E : ℝ × ℕ → Prop) :
    (All[r ← ttcPairLaw atoms φ ε δ cVol cSample; E r])
      ↔ ∀ r : ℝ × ℕ,
          ttcPairLaw atoms φ ε δ cVol cSample {r} ≠ 0 → E r :=
  ae_map_iff_atoms_of_countablyDetermined
    (countablyDetermined_ttcPair atoms φ ε δ cVol cSample) _ E

end Law

#print axioms ttcLaw
#print axioms ttcLaw_def
#print axioms instIsProbabilityMeasureTtcLaw
#print axioms ttcPair
#print axioms ttcPair_def
#print axioms countablyDetermined_ttcPair
#print axioms measurable_ttcPair
#print axioms ttcPairLaw
#print axioms ttcPairLaw_def
#print axioms instIsProbabilityMeasureTtcPairLaw
#print axioms ttcPairLaw_apply
#print axioms PrR_ttcPairLaw
#print axioms PrR_ttcPairLaw_fst
#print axioms ttc_accuracy_pairLaw
#print axioms ttcPairLaw_cost_le
#print axioms ttcPairLaw_cost_le_of_terminates
#print axioms all_ttcPairLaw_cost_le
#print axioms all_ttcPairLaw_iff_atoms

end Ttc

/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import Ttc.Invariants

/-!
# `thm:runtime`: the cost of a run

> Let `m` denote the number of decomposed polytopes. Then `TTC` runs in time
> `O(m·n⁴)`, where `n` is the number of dimensions.

The paper's proof charges two things and asserts they dominate: the main loop runs
**exactly `m` iterations**, each doing one `Vol_ED` call at `O(n⁴)` and drawing
samples at `O(n³)` apiece. This file formalises that accounting.

## What is charged, and why it is a parameter

`Vol_ED` and `GenerateSamples` are *oracles* here (`Ttc.Oracles`) — the model
fixes what they return, never how they compute it — so their per-call costs cannot
be derived and are taken as parameters `cVol` and `cSample`. Leaving them free is
what makes the statement about the *structure* of the run, which is the part this
model can actually see.

**`Ttc.stepCost` charges oracle calls and nothing else.** One unit of `cVol` per
`Vol_ED` call and one unit of `cSample` per sample: this file counts *calls*, and the
per-call prices are inputs to it. `Ttc.runCost_le` is true at every pair of naturals,
including wrong ones, so nothing here makes any particular price correct.

**What the prices denote is fixed elsewhere, and only for two of the three
subroutines.** `Ttc/CostModel.lean` supplies two *derived* cost quantities — quantities
computed from the constructed subroutines' own definitions rather than asserted of them:

* `Ttc.coinCost`, the least number of coins a function of the coin sequence reads.
  `Ttc.coinCost_est_eq` shows the constructed `Vol_ED`'s estimator costs **exactly**
  `Ttc.MonteCarlo.nSamp` coins, and `Ttc.coinCost_ttcVol_le` shows the price list
  `Ttc/Exec/Complexity.lean` §4 charges dominates the derived cost of the run's own
  `vol` field. That is the sense in which `cVol` now denotes something.
* `Ttc.mixCost`, the least ball-walk budget at which the chain's law meets its
  total-variation specification. `Ttc.mixCost_le_mixSteps` and
  `Ttc.mixCost_le_e2eBallWalkSteps` are the proved upper bounds, and are the shape in
  which any future mixing theorem prices `cSample`.

**The sampler's rejection rounds still denote nothing, and cannot.** `Ttc.kv97SampD` is
a density; it consumes no coins and carries no budget, so neither notion applies to it,
and no object in this development performs the rejection loop. Both derived quantities
are also query counts, not machine operations. So instantiating `cVol`/`cSample` at any
concrete arithmetic expression remains an undercount, and neither this file nor
`Ttc/CostModel.lean` proves that `TTC` runs in any amount of time — not the paper's
`O(n⁴)`/`O(n³)`, and not `thm:runtime`'s `O(m·n⁴)`.
`Ttc/Exec/Complexity.lean`'s last section instantiates the prices at the counts the
constructed subroutines carry and says, at length, exactly what that does and does
not establish.

What is **not** a parameter is the shape of the accounting: that the loop runs
`|D|` times, and that iteration `i` hands `GenerateSamples` exactly the Poisson
draw `Nᵢ` that survived the absorption loop. Both are read off `Ttc.step`.

## Two honest gaps, both also in the paper

**The `while` loops are not charged.** The paper's proof charges only the volume
call and the sampling, on the grounds that they dominate. The thinning and Poisson
work of lines 32–35 and 39–42 costs `O(exit level − entry level)` calls per
iteration, and that count has **no deterministic bound** — it is the same quantity
whose finiteness is only high-probability (`Model/Pseudocode`, deviation (a)). So
"they dominate" is not a theorem here, and is not one in the paper either.

**A bounded `Nᵢ` needs the loop to exit.** `thm:runtime` implicitly assumes each
iteration finishes; `Ttc.runCost_le` says so out loud, via `Ttc.AbsorbExits` at
every cube. Off that event the loop never terminates and no time bound is true, so
the hypothesis is not removable — it is what the paper leaves unstated.

Given both, `Ttc.runCost_le` bounds the charged cost by `m · (cVol + cSample ·
Thresh)`: `m` iterations, each one volume call plus at most `Thresh` samples,
because the absorption loop only stops once `Nᵢ + |𝒳| ≤ Thresh`.

## The per-cube price list

`Ttc.runCost`'s two prices are uniform over the cubes, which is fine while they are
free parameters but wrong for any *constructed* subroutine: the Monte-Carlo volume
estimator draws a different number of coins on each cube, and the sampler's chain is
run for a different number of steps on each cube. `Ttc.runCostAt` is the same fold
with `cVol cSample : ι → ℕ`, `Ttc.runCostAt_const` says it degenerates to
`Ttc.runCost` at constant price lists (by `rfl`), `Ttc.runCostAt_le_sum` is the
per-cube bound `∑ᵢ (cVol i + cSample i · Thresh)`, and `Ttc.runCostAt_le_uniform`
recovers `Ttc.runCost_le`'s shape from any uniform upper prices. None of that makes
a price list *correct* — see the previous section.
-/

namespace Ttc

open Multiset

variable {n : ℕ} {ι : Type*} (P : Params) (O : Oracles n ι)

/-- Every cube of the run's own fold satisfies `Ttc.AbsorbExits` — the hypothesis
`thm:runtime` needs and does not state. Quantified over *all* states, which is
what makes it usable under the fold without tracking which state each cube sees. -/
def Terminates (cubes : List ι) : Prop :=
  ∀ (st : SketchState n) (i : ι), i ∈ cubes →
    AbsorbExits P O i (O.vol i) (dropCovered O i st.X) st.level
      (haltLevel P (O.vol i) st.level)

/-- **Each iteration draws at most `Thresh` samples.** The absorption loop stops
only when `Nᵢ + |𝒳| ≤ Thresh`, so the count handed to `GenerateSamples` is at most
`Thresh`. This is where termination is used: below the exit level the guard holds,
and it is the guard *failing* that bounds `Nᵢ`. -/
theorem stepPre_snd_le (st : SketchState n) (i : ι)
    (h : AbsorbExits P O i (O.vol i) (dropCovered O i st.X) st.level
      (haltLevel P (O.vol i) st.level)) :
    ((stepPre P O st i).2 : ℝ) ≤ P.thresh := by
  have hspec := absorbLevel_spec P O i (O.vol i) (dropCovered O i st.X) h
  rw [not_lt] at hspec
  rw [stepPre_snd]
  have hcard : (0 : ℝ) ≤ (card (O.thin st.level (stepPre P O st i).1.level
      (dropCovered O i st.X)) : ℝ) := Nat.cast_nonneg _
  have : (stepPre P O st i).1.level
      = absorbLevel P O i (O.vol i) (dropCovered O i st.X) st.level
          (haltLevel P (O.vol i) st.level) := rfl
  rw [this]
  linarith [hspec]

/-- **The run's charged cost, bounded**: `m` iterations, one volume call each, and
at most `Thresh` samples each.

This is `thm:runtime`'s *accounting*, not its `O(m·n⁴)`. The paper reads that figure
off `cVol = O(n⁴)`, `cSample = O(n³)`, which are its claims about `Vol_ED` and
`GenerateSamples`; this development proves neither and has no cost model in which
either could be stated (module docstring, "What is charged"). What is proved is the
displayed inequality, at *every* `cVol`, `cSample`. -/
theorem runCost_le (cVol cSample : ℕ) (ρ : ℤ) (cubes : List ι) (thr : ℕ)
    (hthr : (thr : ℝ) = P.thresh) (h : Terminates P O cubes) :
    runCost P O cVol cSample ρ cubes ≤ cubes.length * (cVol + cSample * thr) := by
  have key : ∀ (l : List ι), (∀ (st : SketchState n) (i : ι), i ∈ l →
        AbsorbExits P O i (O.vol i) (dropCovered O i st.X) st.level
          (haltLevel P (O.vol i) st.level)) →
      ∀ (st : SketchState n) (acc : ℕ),
      (l.foldl (fun (a : ℕ × SketchState n) i =>
          (a.1 + stepCost cVol cSample (stepPre P O a.2 i).2, step P O ρ a.2 i))
        (acc, st)).1 ≤ acc + l.length * (cVol + cSample * thr) := by
    intro l
    induction l with
    | nil => intro _ st acc; simp
    | cons i rest ih =>
        intro hmem st acc
        have hi := hmem st i List.mem_cons_self
        have hN : (stepPre P O st i).2 ≤ thr := by
          have := stepPre_snd_le P O st i hi
          rw [← hthr] at this
          exact_mod_cast this
        have hstep : stepCost cVol cSample (stepPre P O st i).2 ≤ cVol + cSample * thr :=
          Nat.add_le_add_left (Nat.mul_le_mul_left cSample hN) cVol
        have hrec := ih (fun st' i' hi' => hmem st' i' (List.mem_cons_of_mem _ hi'))
          (step P O ρ st i) (acc + stepCost cVol cSample (stepPre P O st i).2)
        simp only [List.foldl_cons, List.length_cons]
        have hmid : acc + stepCost cVol cSample (stepPre P O st i).2
              + rest.length * (cVol + cSample * thr)
            ≤ acc + (rest.length + 1) * (cVol + cSample * thr) := by
          have := Nat.add_le_add_right (Nat.add_le_add_left hstep acc)
            (rest.length * (cVol + cSample * thr))
          calc acc + stepCost cVol cSample (stepPre P O st i).2
                + rest.length * (cVol + cSample * thr)
              ≤ acc + (cVol + cSample * thr) + rest.length * (cVol + cSample * thr) := this
            _ = acc + (rest.length + 1) * (cVol + cSample * thr) := by ring
        exact le_trans hrec hmid
  have := key cubes h ⟨0, 0⟩ 0
  simpa [runCost] using this

/-! ## The elementary cost model

`Ttc.runCost` above charges two supplied prices and nothing else — in particular nothing
for the removal test of lines 26–30 and nothing for either thinning loop.
`Ttc.elemRunCost` (`Model/Pseudocode`) charges the three elementary costs instead, with
sampling *derived* from them.  These are its bounds.
-/

/-- **The sketch never exceeds `Thresh`.**  The overflow loop exits only when
`Nᵢ + |thin 𝒳| ≤ Thresh`, and the iteration's output sketch is exactly those two pieces
(`Ttc.card_step`), so the bound is the exit guard read forwards.  This is the analogue of
`DnfstreamXt.pepin_correct`'s third conjunct, and it is what makes the removal and thinning
charges — which are proportional to `|𝒳|` — polynomial. -/
theorem card_step_le_thresh (ρ : ℤ) (st : SketchState n) (i : ι)
    (h : AbsorbExits P O i (O.vol i) (dropCovered O i st.X) st.level
      (haltLevel P (O.vol i) st.level)) :
    ((card (step P O ρ st i).X : ℝ)) ≤ P.thresh := by
  have hspec := absorbLevel_spec P O i (O.vol i) (dropCovered O i st.X) h
  rw [not_lt] at hspec
  rw [card_step]
  have hlevel : (stepPre P O st i).1.level
      = absorbLevel P O i (O.vol i) (dropCovered O i st.X) st.level
          (haltLevel P (O.vol i) st.level) := rfl
  rw [stepPre_fst_X, stepPre_snd, hlevel]
  push_cast
  linarith [hspec]

/-- **One iteration, in the elementary cost model, under the loop invariants.**

`Ttc.cubeCost` is bounded by a polynomial in the facet count `r`, the volume call's test
count `Q`, the walk length `T`, the threshold, and the two `while`-loop pass counts. -/
theorem cubeCost_le (r : ℕ) (X : Multiset (Space n)) (e a N Q T thr : ℕ)
    (hX : card X ≤ thr) (hN : N ≤ thr) :
    cubeCost r X e a N Q T
      ≤ n * r * Q + n * r * thr + e * thr + 1 + a * (thr + 1) + thr * (T * (n * r)) := by
  unfold cubeCost volCallCost removalCost earlyPassCost overflowPassCost thinCost
    genCost sampleCost walkStepCost memCost drawCost
  have h1 : Q * (n * r) ≤ n * r * Q := by rw [Nat.mul_comm]
  have h2 : n * r * card X ≤ n * r * thr := Nat.mul_le_mul_left _ hX
  have h3 : e * card X ≤ e * thr := Nat.mul_le_mul_left _ hX
  have h4 : a * (card X + 1) ≤ a * (thr + 1) :=
    Nat.mul_le_mul_left _ (Nat.succ_le_succ hX)
  have h5 : N * (T * (n * r)) ≤ thr * (T * (n * r)) := Nat.mul_le_mul_right _ hN
  omega

/-- **The whole run, in the elementary cost model.**

`m` iterations, each meeting `Ttc.cubeCost_le`.  `E` and `A` bound the two `while` loops'
pass counts; bounding *those* is the remaining analysis — see the module note below.  The
`Ttc.Terminates` guard is the same one `Ttc.runCost_le` carries and is still not removable
(`Exec/Complexity` §2). -/
theorem elemRunCost_le (r Q T thr E A : ℕ) (ρ : ℤ) (cubes : List ι)
    (hT : 0 ≤ P.thresh) (hthr : P.thresh ≤ (thr : ℝ)) (h : Terminates P O cubes)
    (hE : ∀ (st : SketchState n) (i : ι), i ∈ cubes →
      haltLevel P (O.vol i) st.level - st.level ≤ E)
    (hA : ∀ (st : SketchState n) (i : ι), i ∈ cubes →
      (stepPre P O st i).1.level - haltLevel P (O.vol i) st.level ≤ A) :
    elemRunCost P O r Q T ρ cubes
      ≤ cubes.length *
          (n * r * Q + n * r * thr + E * thr + 1 + A * (thr + 1) + thr * (T * (n * r))) := by
  set B := n * r * Q + n * r * thr + E * thr + 1 + A * (thr + 1) + thr * (T * (n * r)) with hB
  have key : ∀ (l : List ι), (∀ (st : SketchState n) (i : ι), i ∈ l →
        AbsorbExits P O i (O.vol i) (dropCovered O i st.X) st.level
          (haltLevel P (O.vol i) st.level)) →
      (∀ (st : SketchState n) (i : ι), i ∈ l →
        haltLevel P (O.vol i) st.level - st.level ≤ E) →
      (∀ (st : SketchState n) (i : ι), i ∈ l →
        (stepPre P O st i).1.level - haltLevel P (O.vol i) st.level ≤ A) →
      ∀ (st : SketchState n) (acc : ℕ), (card st.X : ℝ) ≤ P.thresh →
      (l.foldl (fun (a : ℕ × SketchState n) i =>
          (a.1 + elemStepCost P O r Q T a.2 i, step P O ρ a.2 i)) (acc, st)).1
        ≤ acc + l.length * B := by
    intro l
    induction l with
    | nil => intro _ _ _ st acc _; simp
    | cons i rest ih =>
        intro hmem hEm hAm st acc hst
        have hi := hmem st i List.mem_cons_self
        have hXcard : card (dropCovered O i st.X) ≤ thr := by
          have h1 : card (dropCovered O i st.X) ≤ card st.X := card_dropCovered_le O i st.X
          have h2 : (card st.X : ℝ) ≤ (thr : ℝ) := le_trans hst hthr
          have : card st.X ≤ thr := by exact_mod_cast h2
          omega
        have hN : (stepPre P O st i).2 ≤ thr := by
          have h1 := stepPre_snd_le P O st i hi
          have : ((stepPre P O st i).2 : ℝ) ≤ (thr : ℝ) := le_trans h1 hthr
          exact_mod_cast this
        have hstep : elemStepCost P O r Q T st i ≤ B := by
          rw [hB]
          refine le_trans (cubeCost_le r (dropCovered O i st.X) _ _ _ Q T thr hXcard hN) ?_
          have h3 : (haltLevel P (O.vol i) st.level - st.level) * thr ≤ E * thr :=
            Nat.mul_le_mul_right _ (hEm st i List.mem_cons_self)
          have h4 : ((stepPre P O st i).1.level - haltLevel P (O.vol i) st.level) * (thr + 1)
              ≤ A * (thr + 1) :=
            Nat.mul_le_mul_right _ (hAm st i List.mem_cons_self)
          omega
        have hnext : (card (step P O ρ st i).X : ℝ) ≤ P.thresh :=
          card_step_le_thresh P O ρ st i hi
        have hrec := ih (fun st' i' hi' => hmem st' i' (List.mem_cons_of_mem _ hi'))
          (fun st' i' hi' => hEm st' i' (List.mem_cons_of_mem _ hi'))
          (fun st' i' hi' => hAm st' i' (List.mem_cons_of_mem _ hi'))
          (step P O ρ st i) (acc + elemStepCost P O r Q T st i) hnext
        simp only [List.foldl_cons, List.length_cons]
        refine le_trans hrec ?_
        have : acc + elemStepCost P O r Q T st i + rest.length * B
            ≤ acc + B + rest.length * B := by omega
        calc acc + elemStepCost P O r Q T st i + rest.length * B
            ≤ acc + B + rest.length * B := this
          _ = acc + (rest.length + 1) * B := by ring
  have hstart : ((card (⟨0, 0⟩ : SketchState n).X : ℝ)) ≤ P.thresh := by
    simpa using hT
  have := key cubes h hE hA ⟨0, 0⟩ 0 hstart
  simpa [elemRunCost] using this

#print axioms card_step_le_thresh
#print axioms cubeCost_le
#print axioms elemRunCost_le

/-! ## The same fold with a per-cube price list

`Ttc.runCost` charges the same `cVol` at every cube and the same `cSample` at every
sample.  A *constructed* subroutine does not have one price: the Monte-Carlo
estimator's coin count and the ball walk's step count both depend on the cube's own
geometry.  The three declarations below are the per-cube form of the fold and of its
bound.  They change the shape of the accounting, not its status: a price list is
still an input, and nothing here says any particular list is the cost of anything. -/

/-- **The charged cost with a per-cube price list.**  `Ttc.runCost` with the two
constants replaced by functions of the cube.  The *state* fold is untouched — only
the accumulator changes — so this is the same run, priced differently. -/
noncomputable def runCostAt (cVol cSample : ι → ℕ) (ρ : ℤ) (cubes : List ι) : ℕ :=
  (cubes.foldl
    (fun (acc : ℕ × SketchState n) i =>
      (acc.1 + stepCost (cVol i) (cSample i) (stepPre P O acc.2 i).2, step P O ρ acc.2 i))
    (0, ⟨0, 0⟩)).1

/-- **At constant price lists `Ttc.runCostAt` is `Ttc.runCost`** — by `rfl`, so the
generalisation cannot have quietly changed what is being folded. -/
theorem runCostAt_const (cVol cSample : ℕ) (ρ : ℤ) (cubes : List ι) :
    runCostAt P O (fun _ => cVol) (fun _ => cSample) ρ cubes
      = runCost P O cVol cSample ρ cubes := rfl

/-- **The per-cube cost bound**: `∑ᵢ (cVol i + cSample i · thr)` over the cube list,
for any `thr` at or above `Thresh`.  Same proof as `Ttc.runCost_le`, and the same
`Ttc.Terminates` hypothesis, which is still not removable. -/
theorem runCostAt_le_sum (cVol cSample : ι → ℕ) (ρ : ℤ) (cubes : List ι) (thr : ℕ)
    (hthr : P.thresh ≤ (thr : ℝ)) (h : Terminates P O cubes) :
    runCostAt P O cVol cSample ρ cubes
      ≤ (cubes.map (fun i => cVol i + cSample i * thr)).sum := by
  have key : ∀ (l : List ι), (∀ (st : SketchState n) (i : ι), i ∈ l →
        AbsorbExits P O i (O.vol i) (dropCovered O i st.X) st.level
          (haltLevel P (O.vol i) st.level)) →
      ∀ (st : SketchState n) (acc : ℕ),
      (l.foldl (fun (a : ℕ × SketchState n) i =>
          (a.1 + stepCost (cVol i) (cSample i) (stepPre P O a.2 i).2, step P O ρ a.2 i))
        (acc, st)).1 ≤ acc + (l.map (fun i => cVol i + cSample i * thr)).sum := by
    intro l
    induction l with
    | nil => intro _ st acc; simp
    | cons i rest ih =>
        intro hmem st acc
        have hi := hmem st i List.mem_cons_self
        have hN : (stepPre P O st i).2 ≤ thr := by
          have hle : ((stepPre P O st i).2 : ℝ) ≤ (thr : ℝ) :=
            le_trans (stepPre_snd_le P O st i hi) hthr
          exact_mod_cast hle
        have hstep : stepCost (cVol i) (cSample i) (stepPre P O st i).2
            ≤ cVol i + cSample i * thr :=
          Nat.add_le_add_left (Nat.mul_le_mul_left (cSample i) hN) (cVol i)
        have hrec := ih (fun st' i' hi' => hmem st' i' (List.mem_cons_of_mem _ hi'))
          (step P O ρ st i) (acc + stepCost (cVol i) (cSample i) (stepPre P O st i).2)
        simp only [List.foldl_cons, List.map_cons, List.sum_cons]
        have hmid : acc + stepCost (cVol i) (cSample i) (stepPre P O st i).2
              + (rest.map (fun i => cVol i + cSample i * thr)).sum
            ≤ acc + ((cVol i + cSample i * thr)
                + (rest.map (fun i => cVol i + cSample i * thr)).sum) := by
          have hh := Nat.add_le_add_right (Nat.add_le_add_left hstep acc)
            (rest.map (fun i => cVol i + cSample i * thr)).sum
          calc acc + stepCost (cVol i) (cSample i) (stepPre P O st i).2
                + (rest.map (fun i => cVol i + cSample i * thr)).sum
              ≤ acc + (cVol i + cSample i * thr)
                  + (rest.map (fun i => cVol i + cSample i * thr)).sum := hh
            _ = acc + ((cVol i + cSample i * thr)
                  + (rest.map (fun i => cVol i + cSample i * thr)).sum) := by ring
        exact le_trans hrec hmid
  have hk := key cubes h ⟨0, 0⟩ 0
  simpa [runCostAt] using hk

/-- **The per-cube charge is under `Ttc.runCost_le`'s bound at any uniform upper
prices.**  So the refinement is a refinement: whatever the per-cube list is, the
uniform statement at pointwise-larger constants still covers it. -/
theorem runCostAt_le_uniform (cVol cSample : ι → ℕ) (CV CS : ℕ) (ρ : ℤ)
    (cubes : List ι) (thr : ℕ) (hthr : P.thresh ≤ (thr : ℝ)) (h : Terminates P O cubes)
    (hV : ∀ i ∈ cubes, cVol i ≤ CV) (hS : ∀ i ∈ cubes, cSample i ≤ CS) :
    runCostAt P O cVol cSample ρ cubes ≤ cubes.length * (CV + CS * thr) := by
  refine le_trans (runCostAt_le_sum P O cVol cSample ρ cubes thr hthr h) ?_
  have hle : ∀ x ∈ cubes.map (fun i => cVol i + cSample i * thr), x ≤ CV + CS * thr := by
    intro x hx
    obtain ⟨i, hi, rfl⟩ := List.mem_map.1 hx
    exact Nat.add_le_add (hV i hi) (Nat.mul_le_mul_right thr (hS i hi))
  have hsum := List.sum_le_card_nsmul _ _ hle
  simpa [List.length_map, smul_eq_mul] using hsum

end Ttc

/-! ## Axiom profile -/

#print axioms Ttc.Terminates
#print axioms Ttc.stepPre_snd_le
#print axioms Ttc.runCost_le
#print axioms Ttc.runCostAt
#print axioms Ttc.runCostAt_const
#print axioms Ttc.runCostAt_le_sum
#print axioms Ttc.runCostAt_le_uniform

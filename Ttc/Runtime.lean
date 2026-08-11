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

**There is no cost model below the oracle call.** `Ttc.stepCost` is the *whole* of
this development's notion of cost: one unit of `cVol` per `Vol_ED` call and one unit
of `cSample` per sample. Nothing in the development counts machine operations, and
nothing relates either parameter to the running time of any implementation — not the
paper's `O(n⁴)`/`O(n³)`, and not the constructed subroutines' own step counts either.
Instantiating `cVol`/`cSample` is therefore a *pricing convention*, never a theorem;
`Ttc.runCost_le` is true at every pair of naturals, including wrong ones.
`Ttc/Exec/Complexity.lean`'s last section instantiates them at the counts the
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

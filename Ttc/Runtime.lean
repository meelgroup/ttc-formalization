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
be derived and are taken as parameters `cVol` and `cSample`. Instantiating them at
the paper's `O(n⁴)` and `O(n³)` turns `Ttc.runCost_le` into `thm:runtime`
verbatim; leaving them free is what makes the statement about the *structure* of
the run, which is the part this model can actually see.

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
at most `Thresh` samples each. `thm:runtime` is this with `cVol = O(n⁴)` and
`cSample = O(n³)`, giving `m · O(n⁴)`. -/
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

end Ttc

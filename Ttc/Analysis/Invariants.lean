/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import Ttc.Model.Pseudocode

/-!
# Structural invariants of the modelled execution

The algorithm-shaped facts about `Model/Pseudocode` — what the loop does to `X`
and `p` — and nothing else:

* the coverage filter only removes points (`Ttc.card_dropCovered_le`);
* `p` never increases and stays nonnegative, through both loops
  (`Ttc.halveDown_p`, `Ttc.absorb_p`);
* a state whose guard already fails is a fixpoint (`Ttc.absorb_of_settled`,
  `Ttc.halveDown_of_settled`);
* the output is `|X|/p` of the final state (`Ttc.run_eq`), by definition.

The *distributional* facts — that the output concentrates around
`|Q ∩ 𝕃ⁿ|/10^(ρn)` — are `lem:numlattice`, which this development assumes.

**Termination is deliberately not claimed.** Both `while` loops run on fuel. The
real second loop terminates because repeated thinning eventually brings
`Nᵢ + |X|` under `Thresh` *with high probability*; there is no deterministic
bound, so no fuel-independent termination theorem is available — and asserting
one would be false. What is recorded instead is that a state already satisfying
the guard is a fixpoint (`Ttc.absorb_of_settled`).
-/

namespace Ttc

open Multiset

variable {n : ℕ} {ι : Type*} (P : Params) (O : Oracles n ι)

@[simp]
theorem card_dropCovered_le (i : ι) (X : Multiset (Space n)) :
    card (dropCovered O i X) ≤ card X :=
  card_le_card (Multiset.filter_le _ _)

/-- Thinning does not grow `X` — the cardinality form of `Oracles.halve_le`. -/
@[simp]
theorem card_halve_le (c j : ℕ) (X : Multiset (Space n)) :
    card (O.halve c j X) ≤ card X :=
  card_le_card (O.halve_le c j X)

@[simp]
theorem halveDown_zero (t : ℝ) (st : SketchState n) : halveDown P O t 0 st = st := rfl

@[simp]
theorem absorb_zero (i : ι) (t : ℝ) (s : SketchState n × ℕ) : absorb P O i t 0 s = s := rfl

/-- A state whose guard already fails is a fixpoint of the absorption loop. -/
theorem absorb_of_settled (i : ι) (t : ℝ) (f : ℕ) (s : SketchState n × ℕ)
    (h : ¬ P.thresh < (s.2 : ℝ) + card s.1.X) : absorb P O i t f s = s := by
  cases f with
  | zero => rfl
  | succ f => rw [absorb, if_neg h]

/-- Likewise for the first loop. -/
theorem halveDown_of_settled (t : ℝ) (f : ℕ) (st : SketchState n)
    (h : ¬ P.thresh / t ≤ st.p) : halveDown P O t f st = st := by
  cases f with
  | zero => rfl
  | succ f => rw [halveDown, if_neg h]

/-- **`p` never increases, and stays nonnegative**, through the first loop. -/
theorem halveDown_p (t : ℝ) (f : ℕ) (st : SketchState n) (h : 0 ≤ st.p) :
    0 ≤ (halveDown P O t f st).p ∧ (halveDown P O t f st).p ≤ st.p := by
  induction f generalizing st with
  | zero => exact ⟨h, le_rfl⟩
  | succ f ih =>
      rw [halveDown]
      split
      · have hh : (0:ℝ) ≤ st.p / 2 := by linarith
        obtain ⟨h1, h2⟩ := ih ⟨O.halve st.clock st.level st.X, st.p / 2, st.clock + 1, st.level + 1⟩ hh
        exact ⟨h1, le_trans h2 (by simpa using (by linarith : st.p / 2 ≤ st.p))⟩
      · exact ⟨h, le_rfl⟩

/-- **`p` never increases, and stays nonnegative**, through the second loop. -/
theorem absorb_p (i : ι) (t : ℝ) (f : ℕ) (s : SketchState n × ℕ) (h : 0 ≤ s.1.p) :
    0 ≤ (absorb P O i t f s).1.p ∧ (absorb P O i t f s).1.p ≤ s.1.p := by
  induction f generalizing s with
  | zero => exact ⟨h, le_rfl⟩
  | succ f ih =>
      obtain ⟨st, N⟩ := s
      rw [absorb]
      split
      · have hh : (0:ℝ) ≤ st.p / 2 := by simp at h; linarith
        obtain ⟨h1, h2⟩ := ih (⟨O.halve st.clock st.level st.X, st.p / 2, st.clock + 2, st.level + 1⟩,
          O.pois (st.clock + 1) i (st.level + 1) (t * st.p / 2)) hh
        refine ⟨h1, le_trans h2 ?_⟩
        simp at h ⊢; linarith
      · exact ⟨h, le_rfl⟩

/-- **`X` only grows by the freshly generated samples**: the loop body removes
covered points and thins, then appends exactly `Nᵢ` new ones. -/
theorem card_step (fuel : ℕ) (ρ : ℤ) (st : SketchState n) (i : ι) :
    card (step P O fuel ρ st i).X
      = card (stepPre P O fuel st i).1.X + (stepPre P O fuel st i).2 := by
  simp [step, O.gen_card]

/-! ## The clock

Every randomised call uses the current clock and advances it, so distinct calls
carry distinct indices. That is the whole point of the counter: it is what lets a
distributional hypothesis on `Ttc.Oracles` speak of *independent* draws. -/

/-- The first loop never rewinds the clock. -/
theorem halveDown_clock (t : ℝ) (f : ℕ) (st : SketchState n) :
    st.clock ≤ (halveDown P O t f st).clock := by
  induction f generalizing st with
  | zero => exact le_rfl
  | succ f ih =>
      rw [halveDown]
      split
      · exact le_trans (Nat.le_succ _) (ih ⟨O.halve st.clock st.level st.X, st.p / 2, st.clock + 1, st.level + 1⟩)
      · exact le_rfl

/-- The second loop never rewinds the clock. -/
theorem absorb_clock (i : ι) (t : ℝ) (f : ℕ) (s : SketchState n × ℕ) :
    s.1.clock ≤ (absorb P O i t f s).1.clock := by
  induction f generalizing s with
  | zero => exact le_rfl
  | succ f ih =>
      obtain ⟨st, N⟩ := s
      rw [absorb]
      split
      · refine le_trans ?_ (ih (⟨O.halve st.clock st.level st.X, st.p / 2,
          st.clock + 2, st.level + 1⟩,
          O.pois (st.clock + 1) i (st.level + 1) (t * st.p / 2)))
        show st.clock ≤ st.clock + 2
        omega
      · exact le_rfl

/-- **Each cube strictly advances the clock** — `GenerateSamples` always draws. So
no two iterations of the main loop share a draw. -/
theorem step_clock (fuel : ℕ) (ρ : ℤ) (st : SketchState n) (i : ι) :
    st.clock < (step P O fuel ρ st i).clock := by
  set st₂ := halveDown P O (O.vol i) fuel
    (⟨dropCovered O i st.X, st.p, st.clock, st.level⟩ : SketchState n) with hst₂
  have h₁ : st.clock ≤ st₂.clock :=
    halveDown_clock P O (O.vol i) fuel
      (⟨dropCovered O i st.X, st.p, st.clock, st.level⟩ : SketchState n)
  have h₂ : st₂.clock + 1 ≤ (stepPre P O fuel st i).1.clock :=
    absorb_clock P O i (O.vol i) fuel
      ((⟨st₂.X, st₂.p, st₂.clock + 1, st₂.level⟩ : SketchState n),
        O.pois st₂.clock i st₂.level (O.vol i * st₂.p))
  have h₃ : (step P O fuel ρ st i).clock = (stepPre P O fuel st i).1.clock + 1 := rfl
  omega

/-- The output is `|X|/p` of the final state — true by definition, recorded so
`thm:volumettc`'s statement can be read against the code. -/
theorem run_eq (fuel : ℕ) (ρ : ℤ) (cubes : List ι) :
    run P O fuel ρ cubes =
      (card (cubes.foldl (step P O fuel ρ) ⟨0, 1, 0, 0⟩).X : ℝ) /
        (cubes.foldl (step P O fuel ρ) ⟨0, 1, 0, 0⟩).p := rfl

/-! ## Each loop reads only its own clock window

The state after a stretch of the run depends only on the draws that stretch
consumed. That is what makes it *past-measurable*, which is in turn what lets the
independence of the draws be used: the next draw is independent of everything
computed so far.

These are congruence lemmas — two oracle bundles agreeing on the relevant window
of clocks produce the same state — proved by the same induction as the other
structural facts, with no probability in sight.
-/

/-- **The first loop reads clocks `[st.clock, st.clock + f)`**, at most one per
iteration of its fuel. -/
theorem halveDown_congr {O O' : Oracles n ι} (t : ℝ) :
    ∀ (f : ℕ) (st : SketchState n),
      (∀ c, st.clock ≤ c → c < st.clock + f → O.halve c = O'.halve c) →
      halveDown P O t f st = halveDown P O' t f st := by
  intro f
  induction f with
  | zero => intro st _; rfl
  | succ f ih =>
      intro st hag
      rw [halveDown, halveDown]
      split
      · have h0 : O.halve st.clock = O'.halve st.clock :=
          hag st.clock le_rfl (by omega)
        rw [h0]
        exact ih ⟨O'.halve st.clock st.level st.X, st.p / 2, st.clock + 1, st.level + 1⟩
          (fun c hc hc' => hag c (by simp at hc; omega) (by simp at hc'; omega))
      · rfl

/-- **The second loop reads clocks `[st.clock, st.clock + 2f)`** — two per
iteration: the thinning, then the Poisson. -/
theorem absorb_congr {O O' : Oracles n ι} (i : ι) (t : ℝ) :
    ∀ (f : ℕ) (sN : SketchState n × ℕ),
      (∀ c, sN.1.clock ≤ c → c < sN.1.clock + 2 * f → O.halve c = O'.halve c) →
      (∀ c, sN.1.clock ≤ c → c < sN.1.clock + 2 * f → O.pois c = O'.pois c) →
      absorb P O i t f sN = absorb P O' i t f sN := by
  intro f
  induction f with
  | zero => intro sN _ _; rfl
  | succ f ih =>
      intro sN hah hap
      obtain ⟨st, N⟩ := sN
      rw [absorb, absorb]
      split
      · have h0 : O.halve st.clock = O'.halve st.clock :=
          hah st.clock (le_refl st.clock)
            (show st.clock < st.clock + 2 * (f + 1) by omega)
        have h1 : O.pois (st.clock + 1) = O'.pois (st.clock + 1) :=
          hap (st.clock + 1) (show st.clock ≤ st.clock + 1 by omega)
            (show st.clock + 1 < st.clock + 2 * (f + 1) by omega)
        rw [h0, h1]
        exact ih (⟨O'.halve st.clock st.level st.X, st.p / 2, st.clock + 2, st.level + 1⟩,
            O'.pois (st.clock + 1) i (st.level + 1) (t * st.p / 2))
          (fun c hc hc' => hah c
            (show st.clock ≤ c by have h2 : st.clock + 2 ≤ c := hc; omega)
            (show c < st.clock + 2 * (f + 1) by
              have h2 : c < st.clock + 2 + 2 * f := hc'; omega))
          (fun c hc hc' => hap c
            (show st.clock ≤ c by have h2 : st.clock + 2 ≤ c := hc; omega)
            (show c < st.clock + 2 * (f + 1) by
              have h2 : c < st.clock + 2 + 2 * f := hc'; omega))
      · rfl

/-- **The first loop advances the clock by at most `f`.** The companion upper
bound to `Ttc.halveDown_clock`. -/
theorem halveDown_clock_le (t : ℝ) :
    ∀ (f : ℕ) (st : SketchState n), (halveDown P O t f st).clock ≤ st.clock + f := by
  intro f
  induction f with
  | zero => intro st; exact le_of_eq (by rw [halveDown]; omega)
  | succ f ih =>
      intro st
      rw [halveDown]
      split
      · have h := ih ⟨O.halve st.clock st.level st.X, st.p / 2, st.clock + 1, st.level + 1⟩
        have h2 : (halveDown P O t f ⟨O.halve st.clock st.level st.X, st.p / 2, st.clock + 1, st.level + 1⟩).clock
            ≤ st.clock + 1 + f := h
        omega
      · omega

/-- **The second loop advances the clock by at most `2f`.** -/
theorem absorb_clock_le (i : ι) (t : ℝ) :
    ∀ (f : ℕ) (sN : SketchState n × ℕ),
      (absorb P O i t f sN).1.clock ≤ sN.1.clock + 2 * f := by
  intro f
  induction f with
  | zero =>
      intro sN
      show (absorb P O i t 0 sN).1.clock ≤ sN.1.clock + 2 * 0
      rw [absorb]; omega
  | succ f ih =>
      intro sN
      obtain ⟨st, N⟩ := sN
      rw [absorb]
      split
      · have h := ih (⟨O.halve st.clock st.level st.X, st.p / 2, st.clock + 2, st.level + 1⟩,
          O.pois (st.clock + 1) i (st.level + 1) (t * st.p / 2))
        have h2 : (absorb P O i t f (⟨O.halve st.clock st.level st.X, st.p / 2, st.clock + 2, st.level + 1⟩,
            O.pois (st.clock + 1) i (st.level + 1) (t * st.p / 2))).1.clock ≤ st.clock + 2 + 2 * f := h
        show (absorb P O i t f (⟨O.halve st.clock st.level st.X, st.p / 2, st.clock + 2, st.level + 1⟩,
            O.pois (st.clock + 1) i (st.level + 1) (t * st.p / 2))).1.clock ≤ st.clock + 2 * (f + 1)
        omega
      · omega

/-- **One iteration advances the clock by at most `3·fuel + 2`** — `fuel`
thinnings, one Poisson, `2·fuel` more of each, and the `GenerateSamples` draw. -/
theorem step_clock_le (fuel : ℕ) (ρ : ℤ) (st : SketchState n) (i : ι) :
    (step P O fuel ρ st i).clock ≤ st.clock + (3 * fuel + 2) := by
  set st₂ := halveDown P O (O.vol i) fuel
    (⟨dropCovered O i st.X, st.p, st.clock, st.level⟩ : SketchState n) with hst₂
  have h₁ : st₂.clock ≤ st.clock + fuel :=
    halveDown_clock_le P O (O.vol i) fuel
      (⟨dropCovered O i st.X, st.p, st.clock, st.level⟩ : SketchState n)
  have h₂ : (stepPre P O fuel st i).1.clock ≤ st₂.clock + 1 + 2 * fuel :=
    absorb_clock_le P O i (O.vol i) fuel
      ((⟨st₂.X, st₂.p, st₂.clock + 1, st₂.level⟩ : SketchState n),
        O.pois st₂.clock i st₂.level (O.vol i * st₂.p))
  have h₃ : (step P O fuel ρ st i).clock = (stepPre P O fuel st i).1.clock + 1 := rfl
  omega

/-- **One iteration reads only clocks `[st.clock, st.clock + 3·fuel + 2)`.**

Combining the two loop windows with the two single draws (the Poisson before the
absorption loop and `GenerateSamples` after it). This is the step that makes the
run's state a function of the draws *strictly before* its clock — the hypothesis
every use of the draws' independence needs. -/
theorem step_congr {O O' : Oracles n ι} (hvol : O.vol = O'.vol) (hcov : O.covered = O'.covered)
    (fuel : ℕ) (ρ : ℤ) (st : SketchState n) (i : ι)
    (hah : ∀ c, st.clock ≤ c → c < st.clock + (3 * fuel + 2) → O.halve c = O'.halve c)
    (hap : ∀ c, st.clock ≤ c → c < st.clock + (3 * fuel + 2) → O.pois c = O'.pois c)
    (hag : ∀ c, st.clock ≤ c → c < st.clock + (3 * fuel + 2) → O.gen c = O'.gen c) :
    step P O fuel ρ st i = step P O' fuel ρ st i := by
  have hdc : dropCovered O i st.X = dropCovered O' i st.X := by
    rw [dropCovered, dropCovered, hcov]
  have hti : O.vol i = O'.vol i := by rw [hvol]
  -- the first loop agrees, and lands at the same clock
  have hhd : halveDown P O (O.vol i) fuel ⟨dropCovered O i st.X, st.p, st.clock, st.level⟩
      = halveDown P O' (O'.vol i) fuel ⟨dropCovered O' i st.X, st.p, st.clock, st.level⟩ := by
    rw [hdc, hti]
    refine halveDown_congr P (O'.vol i) fuel _ fun c hc hc' => hah c hc ?_
    have h : c < st.clock + fuel := hc'
    omega
  have hbound : (halveDown P O' (O'.vol i) fuel
      (⟨dropCovered O' i st.X, st.p, st.clock, st.level⟩ : SketchState n)).clock ≤ st.clock + fuel := by
    have := halveDown_clock_le P O' (O'.vol i) fuel
      (⟨dropCovered O' i st.X, st.p, st.clock, st.level⟩ : SketchState n)
    simpa using this
  -- the absorption loop agrees too
  have habs : stepPre P O fuel st i = stepPre P O' fuel st i := by
    simp only [stepPre]
    rw [hhd, hti]
    set st₂ := halveDown P O' (O'.vol i) fuel
      (⟨dropCovered O' i st.X, st.p, st.clock, st.level⟩ : SketchState n) with hst₂
    have hlo : st.clock ≤ st₂.clock :=
      halveDown_clock P O' (O'.vol i) fuel
        (⟨dropCovered O' i st.X, st.p, st.clock, st.level⟩ : SketchState n)
    have hhi : st₂.clock ≤ st.clock + fuel := hbound
    have hpois : O.pois st₂.clock = O'.pois st₂.clock :=
      hap st₂.clock hlo (by omega)
    rw [hpois]
    refine absorb_congr P i (O'.vol i) fuel _ ?_ ?_
    · intro c hc hc'
      have hc1 : st₂.clock + 1 ≤ c := hc
      have hc2 : c < st₂.clock + 1 + 2 * fuel := hc'
      exact hah c (by omega) (by omega)
    · intro c hc hc'
      have hc1 : st₂.clock + 1 ≤ c := hc
      have hc2 : c < st₂.clock + 1 + 2 * fuel := hc'
      exact hap c (by omega) (by omega)
  -- and the final `GenerateSamples` draw is the same
  have hclk : (stepPre P O' fuel st i).1.clock ≤ st.clock + (3 * fuel + 1) := by
    have h₂ : (stepPre P O' fuel st i).1.clock
        ≤ (halveDown P O' (O'.vol i) fuel
            (⟨dropCovered O' i st.X, st.p, st.clock, st.level⟩ : SketchState n)).clock
          + 1 + 2 * fuel :=
      absorb_clock_le P O' i (O'.vol i) fuel _
    omega
  have hgenlo : st.clock ≤ (stepPre P O' fuel st i).1.clock := by
    have h := step_clock P O' fuel ρ st i
    have h2 : st.clock < (stepPre P O' fuel st i).1.clock + 1 := h
    omega
  have hgen : O.gen (stepPre P O' fuel st i).1.clock
      = O'.gen (stepPre P O' fuel st i).1.clock :=
    hag _ hgenlo (by omega)
  simp only [step]
  rw [habs, hgen]

/-- **The whole run reads only clocks below `|cubes|·(3·fuel + 2)`.**

By induction over the cube list, using `Ttc.step_congr` for the head and
`Ttc.step_clock_le` to shift the window. Two consequences matter:

* the run is a function of the draws *strictly before* the current clock, which
  is what lets their independence be used;
* it depends on only **finitely many** draws, so the randomness can be modelled
  by a finite product measure — no infinite-product machinery is needed. -/
theorem foldl_step_congr {O O' : Oracles n ι} (hvol : O.vol = O'.vol)
    (hcov : O.covered = O'.covered) (fuel : ℕ) (ρ : ℤ) :
    ∀ (cubes : List ι) (st : SketchState n),
      (∀ c, st.clock ≤ c → c < st.clock + cubes.length * (3 * fuel + 2) →
        O.halve c = O'.halve c) →
      (∀ c, st.clock ≤ c → c < st.clock + cubes.length * (3 * fuel + 2) →
        O.pois c = O'.pois c) →
      (∀ c, st.clock ≤ c → c < st.clock + cubes.length * (3 * fuel + 2) →
        O.gen c = O'.gen c) →
      cubes.foldl (step P O fuel ρ) st = cubes.foldl (step P O' fuel ρ) st := by
  intro cubes
  induction cubes with
  | nil => intro st _ _ _; rfl
  | cons i rest ih =>
      intro st hah hap hag
      have hlen : (i :: rest).length * (3 * fuel + 2)
          = (3 * fuel + 2) + rest.length * (3 * fuel + 2) := by
        simp [List.length_cons]; ring
      rw [hlen] at hah hap hag
      have hstep : step P O fuel ρ st i = step P O' fuel ρ st i :=
        step_congr P hvol hcov fuel ρ st i
          (fun c hc hc' => hah c hc (by omega))
          (fun c hc hc' => hap c hc (by omega))
          (fun c hc hc' => hag c hc (by omega))
      have hclk : (step P O' fuel ρ st i).clock ≤ st.clock + (3 * fuel + 2) :=
        step_clock_le P O' fuel ρ st i
      have hclk0 : st.clock ≤ (step P O' fuel ρ st i).clock :=
        le_of_lt (step_clock P O' fuel ρ st i)
      simp only [List.foldl_cons, hstep]
      exact ih (step P O' fuel ρ st i)
        (fun c hc hc' => hah c (by omega) (by omega))
        (fun c hc hc' => hap c (by omega) (by omega))
        (fun c hc hc' => hag c (by omega) (by omega))

/-- **The run depends on only finitely many draws** — those below
`|cubes|·(3·fuel + 2)`. -/
theorem run_congr {O O' : Oracles n ι} (hvol : O.vol = O'.vol)
    (hcov : O.covered = O'.covered) (fuel : ℕ) (ρ : ℤ) (cubes : List ι)
    (hah : ∀ c < cubes.length * (3 * fuel + 2), O.halve c = O'.halve c)
    (hap : ∀ c < cubes.length * (3 * fuel + 2), O.pois c = O'.pois c)
    (hag : ∀ c < cubes.length * (3 * fuel + 2), O.gen c = O'.gen c) :
    run P O fuel ρ cubes = run P O' fuel ρ cubes := by
  have h := foldl_step_congr P hvol hcov fuel ρ cubes ⟨0, 1, 0, 0⟩
    (fun c _ hc' => hah c (by simpa using hc'))
    (fun c _ hc' => hap c (by simpa using hc'))
    (fun c _ hc' => hag c (by simpa using hc'))
  rw [run, run, h]

/-! ## The rate is always a level

`p` starts at `1` and is only ever halved, so it is always `2^(−k)` for some `k`.
That `k` is the **level** the paper's `Nois(j)` and `Err(j)` are indexed by; the
event "the run finished at level `j`" is not even statable without it. -/

/-- `st.p = 2^(−k)` for some `k` — the state sits at a level. -/
def IsLevel (st : SketchState n) : Prop := st.p = (1 / 2 : ℝ) ^ st.level

theorem isLevel_start : IsLevel (⟨0, 1, 0, 0⟩ : SketchState n) := by
  show (1:ℝ) = (1 / 2 : ℝ) ^ 0
  norm_num

theorem IsLevel.halve {st : SketchState n} (h : IsLevel st) (X : Multiset (Space n))
    (c : ℕ) : IsLevel ⟨X, st.p / 2, c, st.level + 1⟩ := by
  show st.p / 2 = (1 / 2 : ℝ) ^ (st.level + 1)
  rw [h, pow_succ]
  ring

/-- The first loop keeps the rate on its level. -/
theorem halveDown_isLevel (t : ℝ) :
    ∀ (f : ℕ) (st : SketchState n), IsLevel st → IsLevel (halveDown P O t f st) := by
  intro f
  induction f with
  | zero => intro st h; exact h
  | succ f ih =>
      intro st h
      rw [halveDown]
      split
      · exact ih _ (h.halve _ _)
      · exact h

/-- The second loop keeps the rate on its level. -/
theorem absorb_isLevel (i : ι) (t : ℝ) :
    ∀ (f : ℕ) (sN : SketchState n × ℕ), IsLevel sN.1 → IsLevel (absorb P O i t f sN).1 := by
  intro f
  induction f with
  | zero => intro sN h; exact h
  | succ f ih =>
      intro sN h
      obtain ⟨st, N⟩ := sN
      rw [absorb]
      split
      · exact ih _ (h.halve _ _)
      · exact h

/-- One iteration keeps the rate on its level. -/
theorem step_isLevel (fuel : ℕ) (ρ : ℤ) (st : SketchState n) (i : ι) (h : IsLevel st) :
    IsLevel (step P O fuel ρ st i) := by
  have h2 := halveDown_isLevel P O (O.vol i) fuel
    (⟨dropCovered O i st.X, st.p, st.clock, st.level⟩ : SketchState n) h
  exact absorb_isLevel P O i (O.vol i) fuel _ h2

/-- **The run always ends on a level**: its final rate is `2^(−level)`. -/
theorem foldl_isLevel (fuel : ℕ) (ρ : ℤ) :
    ∀ (cubes : List ι) (st : SketchState n), IsLevel st →
      IsLevel (cubes.foldl (step P O fuel ρ) st) := by
  intro cubes
  induction cubes with
  | nil => intro st h; exact h
  | cons i rest ih => intro st h; exact ih _ (step_isLevel P O fuel ρ st i h)

theorem run_isLevel (fuel : ℕ) (ρ : ℤ) (cubes : List ι) :
    IsLevel (cubes.foldl (step P O fuel ρ) ⟨0, 1, 0, 0⟩) :=
  foldl_isLevel P O fuel ρ cubes _ isLevel_start

/-! ## What `𝒳` can contain

`𝒳` only ever holds points that `GenerateSamples` produced: it starts empty, the
coverage filter and the thinning only *remove* (`Oracles.halve_le`), and the sole
insertion is `gen`. So a support contract on `gen` propagates to the whole run.
This is the first structural step of the coupling: it is what makes the run's
state a count vector over a *fixed finite* set of lattice points.
-/

/-- The first loop only removes points. -/
theorem mem_of_mem_halveDown (t : ℝ) (f : ℕ) (st : SketchState n) {s : Space n}
    (h : s ∈ (halveDown P O t f st).X) : s ∈ st.X := by
  induction f generalizing st with
  | zero => exact h
  | succ f ih =>
      rw [halveDown] at h
      split at h
      · exact Multiset.mem_of_le (O.halve_le st.clock st.level st.X)
          (ih ⟨O.halve st.clock st.level st.X, st.p / 2, st.clock + 1, st.level + 1⟩ h)
      · exact h

/-- The second loop only removes points. -/
theorem mem_of_mem_absorb (i : ι) (t : ℝ) (f : ℕ) (sN : SketchState n × ℕ) {s : Space n}
    (h : s ∈ (absorb P O i t f sN).1.X) : s ∈ sN.1.X := by
  induction f generalizing sN with
  | zero => exact h
  | succ f ih =>
      obtain ⟨st, N⟩ := sN
      rw [absorb] at h
      split at h
      · exact Multiset.mem_of_le (O.halve_le st.clock st.level st.X)
          (ih (⟨O.halve st.clock st.level st.X, st.p / 2, st.clock + 2, st.level + 1⟩,
            O.pois (st.clock + 1) i (st.level + 1) (t * st.p / 2)) h)
      · exact h

/-- **One iteration keeps `𝒳` inside `T`**, given that `GenerateSamples` does for
*this* cube. -/
theorem mem_step {T : Set (Space n)} (fuel : ℕ) (ρ : ℤ) (st : SketchState n) (i : ι)
    (hgen : ∀ c j N, ∀ s ∈ O.gen c i j N ρ, s ∈ T)
    (hst : ∀ s ∈ st.X, s ∈ T) :
    ∀ s ∈ (step P O fuel ρ st i).X, s ∈ T := by
  intro s hs
  rw [step] at hs
  simp only [Multiset.mem_add] at hs
  rcases hs with hs | hs
  · refine hst s ?_
    have h1 := mem_of_mem_absorb P O i (O.vol i) fuel _ hs
    exact Multiset.mem_of_le (Multiset.filter_le _ _)
      (mem_of_mem_halveDown P O (O.vol i) fuel _ h1)
  · exact hgen _ _ _ s hs

/-- **The whole run keeps `𝒳` inside `T`**, needing the `gen` contract only at the
cubes actually processed. -/
theorem mem_foldl_step {T : Set (Space n)} (fuel : ℕ) (ρ : ℤ) :
    ∀ (cubes : List ι), (∀ c i j N, i ∈ cubes → ∀ s ∈ O.gen c i j N ρ, s ∈ T) →
      ∀ (st : SketchState n), (∀ s ∈ st.X, s ∈ T) →
        ∀ s ∈ (cubes.foldl (step P O fuel ρ) st).X, s ∈ T := by
  intro cubes
  induction cubes with
  | nil => intro _ st hst; exact hst
  | cons i rest ih =>
      intro hgen st hst
      refine ih (fun c i' j N hi' => hgen c i' j N (List.mem_cons_of_mem _ hi'))
        (step P O fuel ρ st i) ?_
      exact mem_step P O fuel ρ st i
        (fun c j N => hgen c i j N (List.mem_cons_self ..)) hst

/-- **The run's sample multiset lies in `T`**, whenever `GenerateSamples` does.
Starting from `𝒳 = ∅` the state hypothesis is vacuous, so this is unconditional. -/
theorem mem_run_state {T : Set (Space n)} (fuel : ℕ) (ρ : ℤ) (cubes : List ι)
    (hgen : ∀ c i j N, i ∈ cubes → ∀ s ∈ O.gen c i j N ρ, s ∈ T) :
    ∀ s ∈ (cubes.foldl (step P O fuel ρ) ⟨0, 1, 0, 0⟩).X, s ∈ T :=
  mem_foldl_step P O fuel ρ cubes hgen ⟨0, 1, 0, 0⟩ (by simp)

/-- The algorithm starts from `X = ∅`, `p = 1` (line 22). -/
@[simp]
theorem run_nil (fuel : ℕ) (ρ : ℤ) : run P O fuel ρ ([] : List ι) = 0 := by
  simp [run]

end Ttc

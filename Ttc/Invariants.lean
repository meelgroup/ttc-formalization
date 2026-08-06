/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import Ttc.Model.Pseudocode

/-!
# Structural invariants of the modelled execution

The algorithm-shaped facts about `Model/Pseudocode` — what one iteration does to
`𝒳` and to the level — and nothing else:

* the coverage filter and the thinning only *remove* points
  (`Ttc.card_dropCovered_le`, `Ttc.card_thin_le`, `Ttc.mem_run_state`);
* the level never rewinds (`Ttc.le_haltLevel`, `Ttc.le_absorbLevel`,
  `Ttc.le_step_level`);
* **every level a loop passes through had its guard true** (`Ttc.lt_haltLevel`,
  `Ttc.lt_absorbLevel`) — the exit-level form of "the loop ran";
* the output is `|𝒳|/p` of the final state (`Ttc.run_eq`), by definition.

The *distributional* facts — that the output concentrates around
`|Q ∩ 𝕃ⁿ|/10^(ρn)` — are `lem:numlattice`, proved in `Coupling/NumLattice`.

**Termination is deliberately not claimed, and is not needed.** Both `while` loops
are modelled by their exit level (`Model/Pseudocode`, deviation (a)), so there is
no recursion to terminate. The second loop of the real algorithm exits only with
high probability; what the exit-level model says on a run where it never exits is
"the loop did not move", and the two lemmas this file exports about exit levels —
`Ttc.lt_haltLevel` and `Ttc.lt_absorbLevel` — are then vacuous rather than false.
-/

namespace Ttc

open Multiset

variable {n : ℕ} {ι : Type*} (P : Params) (O : Oracles n ι)

@[simp]
theorem card_dropCovered_le (i : ι) (X : Multiset (Space n)) :
    card (dropCovered O i X) ≤ card X :=
  card_le_card (Multiset.filter_le _ _)

/-- Thinning does not grow `𝒳` — the cardinality form of `Oracles.thin_le`. -/
@[simp]
theorem card_thin_le (j₀ j' : ℕ) (X : Multiset (Space n)) :
    card (O.thin j₀ j' X) ≤ card X :=
  card_le_card (O.thin_le j₀ j' X)

/-! ## The two exit levels

Each `while` loop is the least level at or above the entry level at which its
guard fails (`Model/Pseudocode`, deviation (a)). Two facts follow immediately, and
they are the only ones the development uses: the loop never rewinds the level, and
**every level strictly below the exit level had the guard true**. The second is the
exit-level form of "the loop iterated through that level", and it is what the
trigger arguments of `Coupling/Run` consume.
-/

/-- The first loop never rewinds the level. -/
theorem le_haltLevel (t : ℝ) (j : ℕ) : j ≤ haltLevel P t j := le_max_left _ _

/-- The second loop never rewinds the level. -/
theorem le_absorbLevel (i : ι) (t : ℝ) (X : Multiset (Space n)) (j₀ j₁ : ℕ) :
    j₁ ≤ absorbLevel P O i t X j₀ j₁ := le_max_left _ _

/-- **Every level the first loop passes through has a large rate.** The loop halves
while `Thresh/t ≤ p`, so at every level it crosses, `t·p` is at least `Thresh`.
Deterministic — no randomness enters. -/
theorem lt_haltLevel (t : ℝ) {j j' : ℕ} (hj : j ≤ j') (h : j' < haltLevel P t j) :
    P.thresh / t ≤ (1 / 2 : ℝ) ^ j' := by
  have hlt : j' < sInf {j'' | ¬ P.thresh / t ≤ (1 / 2 : ℝ) ^ j''} := by
    rcases lt_max_iff.1 h with h' | h'
    · exact absurd h' (Nat.not_lt.2 hj)
    · exact h'
  by_contra hcon
  exact absurd (Nat.sInf_le (Set.mem_setOf_eq ▸ hcon)) (Nat.not_le.2 hlt)

/-- **Every level the second loop passes through overflowed**: the level-`j'`
Poisson draw and the surviving sketch together exceeded `Thresh`. -/
theorem lt_absorbLevel (i : ι) (t : ℝ) (X : Multiset (Space n)) {j₀ j₁ j' : ℕ}
    (hj : j₁ ≤ j') (h : j' < absorbLevel P O i t X j₀ j₁) :
    P.thresh < (O.pois i j' (t * (1 / 2 : ℝ) ^ j') : ℝ) + (card (O.thin j₀ j' X) : ℝ) := by
  have hlt : j' < sInf {j'' | j₁ ≤ j'' ∧ ¬ P.thresh <
      (O.pois i j'' (t * (1 / 2 : ℝ) ^ j'') : ℝ) + (card (O.thin j₀ j'' X) : ℝ)} := by
    rcases lt_max_iff.1 h with h' | h'
    · exact absurd h' (Nat.not_lt.2 hj)
    · exact h'
  by_contra hcon
  have hmem : j' ∈ {j'' | j₁ ≤ j'' ∧ ¬ P.thresh <
      (O.pois i j'' (t * (1 / 2 : ℝ) ^ j'') : ℝ) + (card (O.thin j₀ j'' X) : ℝ)} := ⟨hj, hcon⟩
  exact absurd (Nat.sInf_le hmem) (Nat.not_le.2 hlt)

/-! ## When the absorption loop exits

`Ttc.lt_absorbLevel` says what held *below* the exit level, and needs no
termination. The **cost** side needs the complement: what holds *at* it. That is
available exactly when the loop really does exit — when some level at or above the
entry level satisfies the guard's negation — which is the hypothesis
`Ttc.AbsorbExits` below, and is the assumption `thm:runtime` silently makes when
it charges each iteration one `GenerateSamples` call of bounded size. -/

/-- **The absorption loop of one iteration terminates**: some level at or above the
entry level brings `Nᵢ + |𝒳|` back under `Thresh`. Not provable — the real loop
exits only with high probability (`Model/Pseudocode`, deviation (a)) — so it is
carried as a hypothesis wherever the exit state is needed. -/
def AbsorbExits (i : ι) (t : ℝ) (X : Multiset (Space n)) (j₀ j₁ : ℕ) : Prop :=
  {j' | j₁ ≤ j' ∧ ¬ P.thresh <
    (O.pois i j' (t * (1 / 2 : ℝ) ^ j') : ℝ) + (card (O.thin j₀ j' X) : ℝ)}.Nonempty

/-- **At the exit level the guard fails** — the loop stopped because it was
allowed to. Needs `Ttc.AbsorbExits`; with an empty exit set `absorbLevel` is the
entry level and nothing can be said there. -/
theorem absorbLevel_spec (i : ι) (t : ℝ) (X : Multiset (Space n)) {j₀ j₁ : ℕ}
    (h : AbsorbExits P O i t X j₀ j₁) :
    ¬ P.thresh < (O.pois i (absorbLevel P O i t X j₀ j₁)
        (t * (1 / 2 : ℝ) ^ absorbLevel P O i t X j₀ j₁) : ℝ)
      + (card (O.thin j₀ (absorbLevel P O i t X j₀ j₁) X) : ℝ) := by
  obtain ⟨hle, hguard⟩ := Nat.sInf_mem h
  have hmax : absorbLevel P O i t X j₀ j₁ = sInf {j' | j₁ ≤ j' ∧ ¬ P.thresh <
      (O.pois i j' (t * (1 / 2 : ℝ) ^ j') : ℝ) + (card (O.thin j₀ j' X) : ℝ)} :=
    max_eq_right hle
  rw [hmax]
  exact hguard

/-- The sketch one iteration leaves behind: the uncovered points, thinned from the
entry level to the exit level. True by definition, named so proofs can rewrite. -/
theorem stepPre_fst_X (st : SketchState n) (i : ι) :
    (stepPre P O st i).1.X
      = O.thin st.level (stepPre P O st i).1.level (dropCovered O i st.X) := rfl

/-- The Poisson draw one iteration leaves behind: the draw at the exit level. -/
theorem stepPre_snd (st : SketchState n) (i : ι) :
    (stepPre P O st i).2
      = O.pois i (stepPre P O st i).1.level
          (O.vol i * (1 / 2 : ℝ) ^ (stepPre P O st i).1.level) := rfl

/-- The exit level of one iteration is the second loop's. -/
theorem step_level (ρ : ℤ) (st : SketchState n) (i : ι) :
    (step P O ρ st i).level
      = absorbLevel P O i (O.vol i) (dropCovered O i st.X) st.level
          (haltLevel P (O.vol i) st.level) := rfl

/-- One iteration never rewinds the level: both loops only descend in rate. -/
theorem le_stepPre_level (st : SketchState n) (i : ι) :
    st.level ≤ (stepPre P O st i).1.level :=
  le_trans (le_haltLevel P (O.vol i) st.level)
    (le_absorbLevel P O i (O.vol i) (dropCovered O i st.X) st.level _)

/-- One iteration never rewinds the level. -/
theorem le_step_level (ρ : ℤ) (st : SketchState n) (i : ι) :
    st.level ≤ (step P O ρ st i).level :=
  le_stepPre_level P O st i

/-- **`𝒳` only grows by the freshly generated samples**: the loop body removes
covered points and thins, then appends exactly `Nᵢ` new ones. -/
theorem card_step (ρ : ℤ) (st : SketchState n) (i : ι) :
    card (step P O ρ st i).X
      = card (stepPre P O st i).1.X + (stepPre P O st i).2 := by
  simp [step, O.gen_card]

/-- The output is `|𝒳|/p` of the final state — true by definition, recorded so
`thm:volumettc`'s statement can be read against the code. -/
theorem run_eq (ρ : ℤ) (cubes : List ι) :
    run P O ρ cubes =
      (card (cubes.foldl (step P O ρ) ⟨0, 0⟩).X : ℝ) /
        (cubes.foldl (step P O ρ) ⟨0, 0⟩).p := rfl

/-! ## What `𝒳` can contain

`𝒳` only ever holds points that `GenerateSamples` produced: it starts empty, the
coverage filter and the thinning only *remove* (`Oracles.thin_le`), and the sole
insertion is `gen`. So a support contract on `gen` propagates to the whole run.
This is the first structural step of the coupling: it is what makes the run's
state a count vector over a *fixed finite* set of lattice points.
-/

/-- Both loops only remove points. -/
theorem mem_of_mem_stepPre (st : SketchState n) (i : ι) {s : Space n}
    (h : s ∈ (stepPre P O st i).1.X) : s ∈ st.X :=
  Multiset.mem_of_le (Multiset.filter_le _ _)
    (Multiset.mem_of_le (O.thin_le _ _ _) h)

/-- **One iteration keeps `𝒳` inside `T`**, given that `GenerateSamples` does for
*this* cube. -/
theorem mem_step {T : Set (Space n)} (ρ : ℤ) (st : SketchState n) (i : ι)
    (hgen : ∀ j N, ∀ s ∈ O.gen i j N ρ, s ∈ T)
    (hst : ∀ s ∈ st.X, s ∈ T) :
    ∀ s ∈ (step P O ρ st i).X, s ∈ T := by
  intro s hs
  rw [step] at hs
  simp only [Multiset.mem_add] at hs
  rcases hs with hs | hs
  · exact hst s (mem_of_mem_stepPre P O st i hs)
  · exact hgen _ _ s hs

/-- **The whole run keeps `𝒳` inside `T`**, needing the `gen` contract only at the
cubes actually processed. -/
theorem mem_foldl_step {T : Set (Space n)} (ρ : ℤ) :
    ∀ (cubes : List ι), (∀ i j N, i ∈ cubes → ∀ s ∈ O.gen i j N ρ, s ∈ T) →
      ∀ (st : SketchState n), (∀ s ∈ st.X, s ∈ T) →
        ∀ s ∈ (cubes.foldl (step P O ρ) st).X, s ∈ T := by
  intro cubes
  induction cubes with
  | nil => intro _ st hst; exact hst
  | cons i rest ih =>
      intro hgen st hst
      refine ih (fun i' j N hi' => hgen i' j N (List.mem_cons_of_mem _ hi'))
        (step P O ρ st i) ?_
      exact mem_step P O ρ st i (fun j N => hgen i j N (List.mem_cons_self ..)) hst

/-- **The run's sample multiset lies in `T`**, whenever `GenerateSamples` does.
Starting from `𝒳 = ∅` the state hypothesis is vacuous, so this is unconditional. -/
theorem mem_run_state {T : Set (Space n)} (ρ : ℤ) (cubes : List ι)
    (hgen : ∀ i j N, i ∈ cubes → ∀ s ∈ O.gen i j N ρ, s ∈ T) :
    ∀ s ∈ (cubes.foldl (step P O ρ) ⟨0, 0⟩).X, s ∈ T :=
  mem_foldl_step P O ρ cubes hgen ⟨0, 0⟩ (by simp)

/-- The algorithm starts from `𝒳 = ∅` at level `0`, i.e. `p = 1` (line 22). -/
@[simp]
theorem run_nil (ρ : ℤ) : run P O ρ ([] : List ι) = 0 := by
  simp [run]

end Ttc

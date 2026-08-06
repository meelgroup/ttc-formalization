/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import Ttc.Coupling.Family
import Ttc.Invariants

/-!
# The run realises the coupled family

`Ttc.trajOracles` makes the oracles read a trajectory. This file proves the
consequence: along the run, the sample multiset **is** the family at the run's own
level, restricted to the lattice points seen so far. At the end every point has
been seen, so the state is exactly the family at the stopping level — the
pathwise identification README finding 15 says the paper needs and never
constructs.

Everything here is structural. No measure theory: the identification holds on
*every* trajectory that is nested (`hnest`), and nestedness is discharged
separately as an almost-sure property of `Ttc.trajLaw`.
-/

namespace Ttc

open Multiset

variable {L n : ℕ} {ι : Type*}

/-- The state holds the family's level-`st.level` counts, at the points seen so
far and nowhere else. -/
def CoupledAt (pt : Fin L → Space n) (ω : ℕ → (Fin L → ℕ))
    (seen : Fin L → Bool) (st : SketchState n) : Prop :=
  st.X = toMultiset pt fun s => if seen s then ω st.level s else 0

/-- The initial state is coupled, with nothing seen. -/
theorem coupledAt_start (pt : Fin L → Space n) (ω : ℕ → (Fin L → ℕ)) :
    CoupledAt pt ω (fun _ => false) (⟨0, 0⟩ : SketchState n) := by
  show (0 : Multiset (Space n)) = toMultiset pt _
  rw [toMultiset]
  simp

/-- Reading a count off a coupled state. -/
theorem count_of_coupledAt {pt : Fin L → Space n} (hpt : Function.Injective pt)
    {ω : ℕ → (Fin L → ℕ)} {seen : Fin L → Bool} {st : SketchState n}
    (h : CoupledAt pt ω seen st) (s : Fin L) :
    count (pt s) st.X = if seen s then ω st.level s else 0 := by
  rw [h, count_toMultiset hpt]

/-- A nested trajectory is antitone in the level. -/
theorem traj_antitone {ω : ℕ → (Fin L → ℕ)} (hnest : ∀ j s, ω (j + 1) s ≤ ω j s)
    {j j' : ℕ} (h : j ≤ j') (s : Fin L) : ω j' s ≤ ω j s := by
  induction j' with
  | zero => rw [Nat.le_zero.1 h]
  | succ m ih =>
      rcases Nat.lt_or_ge j (m + 1) with hlt | hge
      · exact le_trans (hnest m s) (ih (Nat.lt_succ_iff.1 hlt))
      · rw [Nat.le_antisymm h hge]

/-- **The thinning preserves the coupling.** The oracle returns the family at the
*target* level, capped by what the state holds; on a nested trajectory the cap is
inactive, so the state lands exactly on that level. One lemma covers both `while`
loops, because both are a single jump to their exit level. -/
theorem coupledAt_thin {pt : Fin L → Space n} (hpt : Function.Injective pt)
    {ω : ℕ → (Fin L → ℕ)} (hnest : ∀ j s, ω (j + 1) s ≤ ω j s)
    {vol : ι → ℝ} {covered : Space n → ι → Bool} {mem : ι → Fin L → Bool}
    {seen : Fin L → Bool} {st : SketchState n} (h : CoupledAt pt ω seen st)
    {j' : ℕ} (hj : st.level ≤ j') :
    CoupledAt pt ω seen
      (⟨(trajOracles hpt vol covered mem ω).thin st.level j' st.X, j'⟩ : SketchState n) := by
  show toMultiset pt (fun s => min (ω j' s) (count (pt s) st.X))
      = toMultiset pt fun s => if seen s then ω j' s else 0
  congr 1
  funext s
  rw [count_of_coupledAt hpt h s]
  by_cases hs : seen s
  · simp only [hs, if_true]
    exact min_eq_left (traj_antitone hnest hj s)
  · simp [hs]

/-! ## Restriction: `dropCovered` and `GenerateSamples`

`dropCovered i` deletes the points cube `i` covers; `gen i` puts the family's
counts back on exactly those points. Under `hcov` — the oracle's coverage test
agrees with cube membership on the lattice — the two are inverse, so one iteration
of the main loop sets `seen` to `seen ∨ mem i`.
-/

/-- `Multiset.filter` distributes over a `Finset` sum. -/
theorem filter_finset_sum {α β : Type*} [DecidableEq β] (p : β → Prop) [DecidablePred p]
    (t : Finset α) (f : α → Multiset β) :
    Multiset.filter p (∑ s ∈ t, f s) = ∑ s ∈ t, Multiset.filter p (f s) := by
  classical
  induction t using Finset.induction with
  | empty => simp
  | insert a t ha ih =>
      rw [Finset.sum_insert ha, Finset.sum_insert ha, Multiset.filter_add, ih]

/-- Filtering a `toMultiset` folds the predicate into the count vector. -/
theorem filter_toMultiset {n : ℕ} (pt : Fin L → Space n) (k : Fin L → ℕ)
    (p : Space n → Prop) [DecidablePred p] :
    Multiset.filter p (toMultiset pt k) = toMultiset pt fun s => if p (pt s) then k s else 0 := by
  classical
  rw [toMultiset, toMultiset, filter_finset_sum]
  refine Finset.sum_congr rfl fun s _ => ?_
  by_cases hs : p (pt s)
  · rw [if_pos hs, Multiset.filter_eq_self.2]
    exact fun a ha => by rw [Multiset.eq_of_mem_replicate ha]; exact hs
  · rw [if_neg hs, Multiset.replicate_zero, Multiset.filter_eq_nil.2]
    exact fun a ha => by rw [Multiset.eq_of_mem_replicate ha]; exact hs

/-- **`dropCovered` restricts `seen`.** -/
theorem coupledAt_dropCovered {pt : Fin L → Space n} (hpt : Function.Injective pt)
    {ω : ℕ → (Fin L → ℕ)} {vol : ι → ℝ} {covered : Space n → ι → Bool} {mem : ι → Fin L → Bool}
    (hcov : ∀ s i, covered (pt s) i = mem i s)
    {seen : Fin L → Bool} {st : SketchState n} (h : CoupledAt pt ω seen st) (i : ι) :
    CoupledAt pt ω (fun s => seen s && !mem i s)
      (⟨dropCovered (trajOracles hpt vol covered mem ω) i st.X, st.level⟩ : SketchState n) := by
  classical
  show Multiset.filter _ st.X = _
  rw [h, filter_toMultiset]
  congr 1
  funext s
  have hc : covered (pt s) i = mem i s := hcov s i
  by_cases hm : mem i s = true <;> by_cases hs : seen s = true <;>
    simp [trajOracles, hm, hs, hc]

/-- `toMultiset` is additive in the count vector. -/
theorem toMultiset_add {n : ℕ} (pt : Fin L → Space n) (a b : Fin L → ℕ) :
    toMultiset pt a + toMultiset pt b = toMultiset pt (a + b) := by
  rw [toMultiset, toMultiset, toMultiset, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun s _ => (Multiset.replicate_add _ _ _).symm

/-! ## The two `while` loops

Both are a single jump to an exit level (`Model/Pseudocode`, deviation (a)), so
neither needs an induction: `Ttc.coupledAt_thin` at the exit level is the whole
argument. What the loops *chose* as that level is irrelevant to the coupling — it
matters only to the trigger lemmas further down.
-/

variable {P : Params}

/-- The Poisson draw carried through `Ttc.absorbLevel` is the family's total over
cube `i` **at the level it is drawn at**. -/
def PoisAt (mem : ι → Fin L → Bool) (ω : ℕ → (Fin L → ℕ)) (i : ι) (j N : ℕ) : Prop :=
  N = ∑ s ∈ Finset.univ.filter fun s => mem i s = true, ω j s

/-- For `Ttc.trajOracles` the Poisson draw *is* the family's total — by
definition, at every level and whatever rate it is handed. -/
theorem poisAt_trajOracles {pt : Fin L → Space n} (hpt : Function.Injective pt)
    {vol : ι → ℝ} {covered : Space n → ι → Bool} {mem : ι → Fin L → Bool}
    (ω : ℕ → (Fin L → ℕ)) (i : ι) (j : ℕ) (lam : ℝ) :
    PoisAt mem ω i j ((trajOracles hpt vol covered mem ω).pois i j lam) := rfl

/-! ## One iteration of the main loop -/

/-- **One iteration adds cube `i` to the seen set.** `dropCovered` deletes the
points cube `i` covers and `GenerateSamples` puts the family's counts back on
exactly those points, so the net effect on the count vector is `seen ∨ mem i`.

The `Ttc.Oracles.gen_card` fallback branch is *not* taken: `Ttc.PoisAt` says the
`N` handed to `gen` is precisely the size of the family's restriction to cube `i`
at the state's own level. -/
theorem coupledAt_step {pt : Fin L → Space n} (hpt : Function.Injective pt)
    {ω : ℕ → (Fin L → ℕ)} (hnest : ∀ j s, ω (j + 1) s ≤ ω j s)
    {vol : ι → ℝ} {covered : Space n → ι → Bool} {mem : ι → Fin L → Bool}
    (hcov : ∀ s i, covered (pt s) i = mem i s)
    (P : Params) (ρ : ℤ)
    {seen : Fin L → Bool} {st : SketchState n} (h : CoupledAt pt ω seen st) (i : ι) :
    CoupledAt pt ω (fun s => seen s || mem i s)
      (step P (trajOracles hpt vol covered mem ω) ρ st i) := by
  classical
  set O := trajOracles hpt vol covered mem ω with hO
  set J := (stepPre P O st i).1.level with hJ
  have hj : st.level ≤ J := le_stepPre_level P O st i
  have hres : (stepPre P O st i).1.X
      = toMultiset pt fun s => if seen s && !mem i s then ω J s else 0 := by
    rw [stepPre_fst_X]
    exact coupledAt_thin hpt hnest (coupledAt_dropCovered (vol := vol) hpt hcov h i) hj
  have hresN : PoisAt mem ω i J (stepPre P O st i).2 := by
    rw [stepPre_snd]; exact poisAt_trajOracles hpt ω i J _
  -- the family restricted to cube `i`, at the exit level
  set fam : Multiset (Space n) :=
    toMultiset pt (fun s => if mem i s then ω J s else 0) with hfam
  have hcard : Multiset.card fam = (stepPre P O st i).2 := by
    rw [hfam, card_toMultiset, hresN, Finset.sum_filter]
  have hgen : O.gen i J (stepPre P O st i).2 ρ = fam := by
    show (if Multiset.card (toMultiset pt fun s => if mem i s then ω J s else 0)
        = (stepPre P O st i).2
      then toMultiset pt (fun s => if mem i s then ω J s else 0)
      else Multiset.replicate (stepPre P O st i).2 (padPoint pt mem i)) = fam
    rw [if_pos hcard]
  show (stepPre P O st i).1.X + O.gen i J (stepPre P O st i).2 ρ
      = toMultiset pt fun s => if seen s || mem i s then ω J s else 0
  rw [hgen, hfam, hres, toMultiset_add]
  congr 1
  funext s
  by_cases hm : mem i s = true <;> by_cases hs : seen s = true <;> simp [hm, hs]

/-! ## The whole run

Folding `Ttc.coupledAt_step` over the cube list: after processing a prefix, the
state holds the family at the run's own level on exactly the points some cube of
that prefix covers. When the cubes cover every lattice point, the final state
**is** the family at the stopping level — and its cardinality, the numerator of
the algorithm's output, is that level's total.

This is the identification README finding 15 records as missing from the paper:
`lem:process` gives equality *in law* at each level, but the union bound over
epochs needs the run and the level process to agree *pathwise*. Here they do, by
construction.
-/

/-- **The fold accumulates the seen set.** -/
theorem coupledAt_foldl {pt : Fin L → Space n} (hpt : Function.Injective pt)
    {ω : ℕ → (Fin L → ℕ)} (hnest : ∀ j s, ω (j + 1) s ≤ ω j s)
    {vol : ι → ℝ} {covered : Space n → ι → Bool} {mem : ι → Fin L → Bool}
    (hcov : ∀ s i, covered (pt s) i = mem i s) (P : Params) (ρ : ℤ) :
    ∀ (l : List ι) (seen : Fin L → Bool) (st : SketchState n), CoupledAt pt ω seen st →
      CoupledAt pt ω (fun s => seen s || l.any fun i => mem i s)
        (l.foldl (step P (trajOracles hpt vol covered mem ω) ρ) st) := by
  intro l
  induction l with
  | nil => intro seen st h; simpa using h
  | cons i l ih =>
      intro seen st h
      have := ih (fun s => seen s || mem i s)
        (step P (trajOracles hpt vol covered mem ω) ρ st i)
        (coupledAt_step (vol := vol) hpt hnest hcov P ρ h i)
      refine cast (congrArg (fun f => CoupledAt pt ω f _) ?_) this
      funext s
      simp [List.any_cons, Bool.or_assoc]

/-- **The run realises the family.** With the cubes covering every lattice point,
the algorithm's `|𝒳|` is the level process's total at the run's own stopping
level — pathwise, on every nested trajectory. -/
theorem card_run_eq_sum_traj {pt : Fin L → Space n} (hpt : Function.Injective pt)
    {ω : ℕ → (Fin L → ℕ)} (hnest : ∀ j s, ω (j + 1) s ≤ ω j s)
    {vol : ι → ℝ} {covered : Space n → ι → Bool} {mem : ι → Fin L → Bool}
    (hcov : ∀ s i, covered (pt s) i = mem i s) (P : Params) (ρ : ℤ)
    (l : List ι) (hall : ∀ s, (l.any fun i => mem i s) = true) :
    Multiset.card (l.foldl (step P (trajOracles hpt vol covered mem ω) ρ)
        (⟨0, 0⟩ : SketchState n)).X
      = ∑ s, ω (l.foldl (step P (trajOracles hpt vol covered mem ω) ρ)
          (⟨0, 0⟩ : SketchState n)).level s := by
  have h := coupledAt_foldl (vol := vol) hpt hnest hcov P ρ l (fun _ => false)
    (⟨0, 0⟩ : SketchState n) (coupledAt_start pt ω)
  rw [show (l.foldl (step P (trajOracles hpt vol covered mem ω) ρ)
      (⟨0, 0⟩ : SketchState n)).X = _ from h, card_toMultiset]
  exact Finset.sum_congr rfl fun s _ => by simp [hall s]

/-- **The algorithm's output, in terms of the family.** `|𝒳|/p` with `p = 2^(−J)`
is `2^J` times the level-`J` total. Every quantity on the right is a function of
the trajectory and the run's own stopping level. -/
theorem run_eq_traj {pt : Fin L → Space n} (hpt : Function.Injective pt)
    {ω : ℕ → (Fin L → ℕ)} (hnest : ∀ j s, ω (j + 1) s ≤ ω j s)
    {vol : ι → ℝ} {covered : Space n → ι → Bool} {mem : ι → Fin L → Bool}
    (hcov : ∀ s i, covered (pt s) i = mem i s) (P : Params) (ρ : ℤ)
    (l : List ι) (hall : ∀ s, (l.any fun i => mem i s) = true) :
    run P (trajOracles hpt vol covered mem ω) ρ l
      = 2 ^ (l.foldl (step P (trajOracles hpt vol covered mem ω) ρ)
            (⟨0, 0⟩ : SketchState n)).level
        * (∑ s, ω (l.foldl (step P (trajOracles hpt vol covered mem ω) ρ)
            (⟨0, 0⟩ : SketchState n)).level s : ℕ) := by
  have hcard := card_run_eq_sum_traj (vol := vol) hpt hnest hcov P ρ l hall
  show (Multiset.card _ : ℝ) / (1 / 2 : ℝ) ^ _ = _
  rw [hcard, one_div, inv_pow, div_inv_eq_mul, mul_comm]

/-! ## What `GenerateSamples` returns

`Ttc.TtcProb.gen_mem` asks that the points `gen` hands back really are lattice
points of the cube. For `Ttc.trajOracles` that is inherited from the enumeration:
the main branch returns points `pt s` with `mem i s`, and the never-taken filler
branch returns `Ttc.padPoint`, which is drawn from the cube's own points whenever
it has any. `hne` is the guard that makes the filler safe.
-/

/-- Membership in a `Ttc.toMultiset` comes from a point with a positive count. -/
theorem mem_toMultiset {n : ℕ} {pt : Fin L → Space n} {k : Fin L → ℕ} {x : Space n}
    (hx : x ∈ toMultiset pt k) : ∃ s, pt s = x ∧ 0 < k s := by
  classical
  rw [toMultiset] at hx
  obtain ⟨s, -, hs⟩ := Multiset.mem_sum.1 hx
  rw [Multiset.mem_replicate] at hs
  exact ⟨s, hs.2.symm, Nat.pos_of_ne_zero hs.1⟩

/-- **`Ttc.trajOracles` respects the cube.** -/
theorem gen_mem_trajOracles {pt : Fin L → Space n} (hpt : Function.Injective pt)
    {vol : ι → ℝ} {covered : Space n → ι → Bool} {mem : ι → Fin L → Bool}
    (ω : ℕ → (Fin L → ℕ)) {T : ι → Set (Space n)}
    (hmem : ∀ i s, mem i s = true → pt s ∈ T i) {i : ι} (hne : ∃ s, mem i s = true)
    (j N : ℕ) (r : ℤ) :
    ∀ x ∈ (trajOracles hpt vol covered mem ω).gen i j N r, x ∈ T i := by
  classical
  intro x hx
  simp only [trajOracles] at hx
  split at hx
  · obtain ⟨s, hs, hpos⟩ := mem_toMultiset hx
    by_cases hm : mem i s = true
    · rw [← hs]; exact hmem i s hm
    · simp [hm] at hpos
  · rw [Multiset.eq_of_mem_replicate hx, padPoint, dif_pos hne]
    exact hmem i _ hne.choose_spec

/-! ## The halving trigger

The absorption loop halts at the first level where `Nᵢ + |𝒳| ≤ Thresh`, so every
level strictly below its exit level had `Thresh < Nᵢ + |𝒳|` (`Ttc.lt_absorbLevel`).
Under the coupling both summands read off the *same* level of the family, on
**disjoint** point sets — `𝒳` holds the points seen and not covered by cube `i`,
`Nᵢ` counts exactly the points cube `i` does cover. So the trigger implies
`Thresh < ∑ₛ ω(j)ₛ`: every level the absorption loop passes through is one where
the family's total exceeded `Thresh`. That is the event `Ttc.trajLaw_noise_le`
estimates.

No induction is needed anywhere in this section: the loops are exit levels, so
"the loop passed through `j`" is `j < exit level`, and `Ttc.lt_haltLevel` /
`Ttc.lt_absorbLevel` read the guard off directly.
-/

/-- **The trigger quantity is at most the level total.** `dropCovered` and
`GenerateSamples` partition the points, so `|𝒳| + Nᵢ` never double-counts. -/
theorem card_add_pois_le {pt : Fin L → Space n}
    {ω : ℕ → (Fin L → ℕ)} {mem : ι → Fin L → Bool} {i : ι} {seen : Fin L → Bool}
    {X : Multiset (Space n)} {j N : ℕ}
    (h : CoupledAt pt ω (fun s => seen s && !mem i s) (⟨X, j⟩ : SketchState n))
    (hN : PoisAt mem ω i j N) :
    Multiset.card X + N ≤ ∑ s, ω j s := by
  classical
  rw [show X = _ from h, card_toMultiset, hN, Finset.sum_filter, ← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun s _ => ?_
  by_cases hm : mem i s = true <;> by_cases hs : seen s = true <;> simp [hm, hs]

/-- **Every level one iteration crosses is triggered.** Either it was a first-loop
level — cube `i`'s rate `vol i · p` was at least `Thresh` — or a second-loop level,
where the family's total exceeded `Thresh`. -/
theorem step_trigger {pt : Fin L → Space n} (hpt : Function.Injective pt)
    {ω : ℕ → (Fin L → ℕ)} (hnest : ∀ j s, ω (j + 1) s ≤ ω j s)
    {vol : ι → ℝ} {covered : Space n → ι → Bool} {mem : ι → Fin L → Bool}
    (hcov : ∀ s i, covered (pt s) i = mem i s) (P : Params) (ρ : ℤ)
    {seen : Fin L → Bool} {st : SketchState n} (h : CoupledAt pt ω seen st) (i : ι) :
    ∀ j, st.level ≤ j → j < (step P (trajOracles hpt vol covered mem ω) ρ st i).level →
      P.thresh / vol i ≤ (1 / 2 : ℝ) ^ j ∨ P.thresh < (∑ s, ω j s : ℕ) := by
  classical
  intro j hj hlt
  set O := trajOracles hpt vol covered mem ω with hO
  by_cases hcase : j < haltLevel P (O.vol i) st.level
  · exact Or.inl (lt_haltLevel P (O.vol i) hj hcase)
  refine Or.inr ?_
  -- the second loop was still running at level `j`, so its guard held there
  have htrig := lt_absorbLevel P O i (O.vol i) (dropCovered O i st.X)
    (Nat.not_lt.1 hcase) (by rw [step_level] at hlt; exact hlt)
  -- and at level `j` both summands read off the family
  have hX : CoupledAt pt ω (fun s => seen s && !mem i s)
      (⟨O.thin st.level j (dropCovered O i st.X), j⟩ : SketchState n) :=
    coupledAt_thin hpt hnest (coupledAt_dropCovered (vol := vol) hpt hcov h i) hj
  have hle := card_add_pois_le hX
    (poisAt_trajOracles (vol := vol) (covered := covered) hpt ω i j
      (O.vol i * (1 / 2 : ℝ) ^ j))
  have hcast := (Nat.cast_le (α := ℝ)).2 hle
  rw [Nat.cast_add] at hcast
  linarith

/-- **Every level the whole run crosses is triggered**, by some cube's rate or by
the family's total. -/
theorem foldl_trigger {pt : Fin L → Space n} (hpt : Function.Injective pt)
    {ω : ℕ → (Fin L → ℕ)} (hnest : ∀ j s, ω (j + 1) s ≤ ω j s)
    {vol : ι → ℝ} {covered : Space n → ι → Bool} {mem : ι → Fin L → Bool}
    (hcov : ∀ s i, covered (pt s) i = mem i s) (P : Params) (ρ : ℤ) :
    ∀ (l : List ι) (seen : Fin L → Bool) (st : SketchState n),
      CoupledAt pt ω seen st →
      ∀ j, st.level ≤ j →
        j < (l.foldl (step P (trajOracles hpt vol covered mem ω) ρ) st).level →
        (∃ i ∈ l, P.thresh / vol i ≤ (1 / 2 : ℝ) ^ j) ∨ P.thresh < (∑ s, ω j s : ℕ) := by
  intro l
  induction l with
  | nil => intro seen st _ j hj hlt; exact absurd hlt (Nat.not_lt.2 hj)
  | cons i l ih =>
      intro seen st h j hj hlt
      by_cases hcase : j < (step P (trajOracles hpt vol covered mem ω) ρ st i).level
      · rcases step_trigger (vol := vol) hpt hnest hcov P ρ h i j hj hcase with hA | hB
        · exact Or.inl ⟨i, List.mem_cons_self, hA⟩
        · exact Or.inr hB
      · have := ih (fun s => seen s || mem i s)
          (step P (trajOracles hpt vol covered mem ω) ρ st i)
          (coupledAt_step (vol := vol) hpt hnest hcov P ρ h i)
          j (Nat.not_lt.1 hcase) hlt
        rcases this with ⟨i', hi', hA⟩ | hB
        · exact Or.inl ⟨i', List.mem_cons_of_mem _ hi', hA⟩
        · exact Or.inr hB

/-- **The level cap is a tail event.** Once every cube's rate has fallen below
`Thresh`, the first loop cannot fire, so reaching level `j*` forces the family's
total at level `j*−1` to have exceeded `Thresh`. -/
theorem level_cap_subset {pt : Fin L → Space n} (hpt : Function.Injective pt)
    {ω : ℕ → (Fin L → ℕ)} (hnest : ∀ j s, ω (j + 1) s ≤ ω j s)
    {vol : ι → ℝ} {covered : Space n → ι → Bool} {mem : ι → Fin L → Bool}
    (hcov : ∀ s i, covered (pt s) i = mem i s) (P : Params) (ρ : ℤ)
    (l : List ι) (jstar : ℕ) (hj1 : 1 ≤ jstar)
    (hsmall : ∀ i ∈ l, ¬ (P.thresh / vol i ≤ (1 / 2 : ℝ) ^ (jstar - 1)))
    (hJ : jstar ≤ (l.foldl (step P (trajOracles hpt vol covered mem ω) ρ)
      (⟨0, 0⟩ : SketchState n)).level) :
    P.thresh < (∑ s, ω (jstar - 1) s : ℕ) := by
  rcases foldl_trigger (vol := vol) hpt hnest hcov P ρ l (fun _ => false)
      (⟨0, 0⟩ : SketchState n) (coupledAt_start pt ω) (jstar - 1)
      (Nat.zero_le _) (lt_of_lt_of_le (Nat.sub_lt hj1 Nat.one_pos) hJ) with ⟨i, hi, hA⟩ | hB
  · exact absurd hA (hsmall i hi)
  · exact hB

/-! ## The epoch estimates, transported to the trajectory space

`Ttc.map_trajLaw_eval` says level `j` of the coupled family carries `levelLaw θ j`.
So every estimate proved for a single level — `Ttc.levelLaw_err_le`,
`Ttc.levelLaw_noise_le` — transports to an event of the *trajectory* measure,
where all levels live on one space and can be union-bounded.
-/

open MeasureTheory

/-- Every subset of the count-vector space is measurable: it is countable and
discrete. -/
theorem measurableSet_count {L : ℕ} (A : Set (Fin L → ℕ)) : MeasurableSet A :=
  (Set.to_countable A).measurableSet

/-- Pulling an event of level `j` back to the trajectory space. -/
theorem trajLaw_real_eval {L : ℕ} {θ : Fin L → ℝ} (hθ : ∀ s, 0 ≤ θ s) (j : ℕ)
    (A : Set (Fin L → ℕ)) :
    (trajLaw θ).real {ω | ω j ∈ A} = (levelLaw θ j).real A := by
  rw [← map_trajLaw_eval hθ j]
  rw [Measure.real, Measure.real,
    Measure.map_apply (measurable_pi_apply j) (measurableSet_count A)]
  rfl

/-- **`Err(j)` on the trajectory space.** -/
theorem trajLaw_err_le {L : ℕ} {θ : Fin L → ℝ} {ε : ℝ} (hθ0 : ∀ i, 0 ≤ θ i)
    (hθ : 0 < ∑ i, θ i) (hε0 : 0 < ε) (hε1 : ε ≤ 1) (j : ℕ) :
    (trajLaw θ).real
        {ω | ¬ ((1 - ε) * totalRate θ j ≤ (∑ s, ω j s : ℕ) ∧
              ((∑ s, ω j s : ℕ) : ℝ) ≤ (1 + ε) * totalRate θ j)}
      ≤ 2 * Real.exp (-(ε ^ 2 * totalRate θ j / 3)) := by
  have h := trajLaw_real_eval hθ0 j
    {r : Fin L → ℕ | ¬ ((1 - ε) * totalRate θ j ≤ (∑ s, r s : ℕ) ∧
      ((∑ s, r s : ℕ) : ℝ) ≤ (1 + ε) * totalRate θ j)}
  rw [show {ω : ℕ → (Fin L → ℕ) | ¬ ((1 - ε) * totalRate θ j ≤ (∑ s, ω j s : ℕ) ∧
      ((∑ s, ω j s : ℕ) : ℝ) ≤ (1 + ε) * totalRate θ j)}
    = {ω : ℕ → (Fin L → ℕ) | ω j ∈ {r : Fin L → ℕ | ¬ ((1 - ε) * totalRate θ j ≤ (∑ s, r s : ℕ) ∧
      ((∑ s, r s : ℕ) : ℝ) ≤ (1 + ε) * totalRate θ j)}} from rfl, h]
  exact levelLaw_err_le hθ0 hθ hε0 hε1 j

/-- **The overflow estimate on the trajectory space.** -/
theorem trajLaw_noise_le {L : ℕ} {θ : Fin L → ℝ} {Thresh : ℝ} (hθ0 : ∀ i, 0 ≤ θ i)
    (hθ : 0 < ∑ i, θ i) (j : ℕ) (hrate : 2 * totalRate θ j ≤ Thresh) :
    (trajLaw θ).real {ω | Thresh ≤ (∑ s, ω j s : ℕ)} ≤ Real.exp (-(Thresh / 6)) := by
  have h := trajLaw_real_eval hθ0 j {r : Fin L → ℕ | Thresh ≤ (∑ s, r s : ℕ)}
  rw [show {ω : ℕ → (Fin L → ℕ) | Thresh ≤ (∑ s, ω j s : ℕ)}
    = {ω : ℕ → (Fin L → ℕ) | ω j ∈ {r : Fin L → ℕ | Thresh ≤ (∑ s, r s : ℕ)}} from rfl, h]
  exact levelLaw_noise_le hθ0 hθ j hrate

/-! ## The family is nested

Thinning can only remove copies, so `ω(j+1)ₛ ≤ ω(j)ₛ` almost surely. This is what
makes `Ttc.trajOracles`' cap inactive on the run — every result above is stated
for nested trajectories, and this is where that hypothesis is discharged.
-/

open ProbabilityTheory in
/-- A binomial never exceeds its number of trials. -/
theorem binomial_half_gt_null (k : ℕ) : binomial k half {j : ℕ | k < j} = 0 := by
  rw [show {j : ℕ | k < j} = ⋃ j ∈ {j : ℕ | k < j}, ({j} : Set ℕ) from
    (Set.biUnion_of_singleton _).symm, measure_biUnion_null_iff (Set.to_countable _)]
  intro j hj
  rw [binomial_half_singleton, binHalfPMF]
  simp [Nat.choose_eq_zero_of_lt hj]

open ProbabilityTheory in
/-- **One thinning step never increases any count.** -/
theorem thinKernel_le_null {L : ℕ} (k : Fin L → ℕ) :
    thinKernel L k {y : Fin L → ℕ | ¬ ∀ s, y s ≤ k s} = 0 := by
  rw [thinKernel_apply, show {y : Fin L → ℕ | ¬ ∀ s, y s ≤ k s}
      = ⋃ s : Fin L, (Function.eval s) ⁻¹' {j : ℕ | k s < j} from by
    ext y
    constructor
    · intro hy
      rw [Set.mem_setOf_eq, not_forall] at hy
      obtain ⟨s, hs⟩ := hy
      exact Set.mem_iUnion.2 ⟨s, Nat.lt_of_not_le hs⟩
    · rintro hy hall
      obtain ⟨s, hs⟩ := Set.mem_iUnion.1 hy
      exact absurd (hall s) (Nat.not_le.2 hs)]
  refine measure_iUnion_null fun s => ?_
  rw [← Measure.map_apply (measurable_pi_apply s) (Set.to_countable _).measurableSet,
    (MeasureTheory.measurePreserving_eval (fun s => binomial (k s) half) s).map_eq]
  exact binomial_half_gt_null (k s)

open ProbabilityTheory in
/-- One level of the trajectory dominates the next. -/
theorem trajLaw_step_null {L : ℕ} (θ : Fin L → ℝ) (a : ℕ) :
    (trajLaw θ) {ω | ¬ ∀ s, ω (a + 1) s ≤ ω a s} = 0 := by
  set μ₀ : Measure (Fin L → ℕ) := Measure.pi fun s => poissonMeasure (θ s).toNNReal with hμ₀
  have hjoint := Kernel.map_frestrictLe_trajMeasure_compProd_eq_map_trajMeasure
    (X := fun _ : ℕ => (Fin L → ℕ)) (μ₀ := μ₀) (κ := chainKernel L) (a := a)
  set T : Set (((i : ↥(Finset.Iic a)) → (Fin L → ℕ)) × (Fin L → ℕ)) :=
    {hy | ¬ ∀ s, hy.2 s ≤ hy.1 ⟨a, Finset.mem_Iic.2 le_rfl⟩ s} with hT
  have hTm : MeasurableSet T := (Set.to_countable T).measurableSet
  have hpre : {ω : ℕ → (Fin L → ℕ) | ¬ ∀ s, ω (a + 1) s ≤ ω a s}
      = (fun x : ℕ → (Fin L → ℕ) => (Preorder.frestrictLe a x, x (a + 1))) ⁻¹' T := rfl
  rw [trajLaw, hpre, ← Measure.map_apply (by fun_prop) hTm, ← hjoint,
    Measure.compProd_apply hTm]
  refine (lintegral_eq_zero_iff (Kernel.measurable_kernel_prodMk_left hTm)).2 ?_
  filter_upwards with h
  show (chainKernel L a h) _ = 0
  rw [chainKernel]
  exact thinKernel_le_null _

/-- **The coupled family is nested almost surely.** -/
theorem trajLaw_ae_nested {L : ℕ} (θ : Fin L → ℝ) :
    ∀ᵐ ω ∂(trajLaw θ), ∀ j s, ω (j + 1) s ≤ ω j s := by
  rw [MeasureTheory.ae_iff]
  refine measure_mono_null (t := ⋃ a : ℕ, {ω | ¬ ∀ s, ω (a + 1) s ≤ ω a s}) ?_
    (measure_iUnion_null fun a => trajLaw_step_null θ a)
  intro ω hω
  rw [Set.mem_setOf_eq, not_forall] at hω
  obtain ⟨a, ha⟩ := hω
  exact Set.mem_iUnion.2 ⟨a, by simpa using ha⟩

/-! ## The union bound over epochs

The failure event decomposes: either the run halved past `j*` levels, or it
stopped at some `j < j*` where the level-`j` total missed its window. The second
branch is `Err(j)`, estimated above; the first is what `Thresh` controls.

`hwin` is the deterministic link between the family's total rate `∑θ` and the
lattice count `L` — supplied by `lem:lattice`, not by any probability estimate.
-/

/-- **The epoch union bound.** Off the `Err` epochs and below the level cap, the
output is pinned to `(1±ε')·∑θ`, hence to the target window. -/
theorem traj_failure_le {L : ℕ} {θ : Fin L → ℝ} {epsP ε Lval : ℝ}
    (hθ0 : ∀ i, 0 ≤ θ i) (hθ : 0 < ∑ i, θ i) (hep0 : 0 < epsP) (hep1 : epsP ≤ 1)
    (hlo : (1 - ε / 2) * Lval ≤ (1 - epsP) * (∑ s, θ s))
    (hhi : (1 + epsP) * (∑ s, θ s) ≤ (1 + ε / 2) * Lval)
    (J : (ℕ → (Fin L → ℕ)) → ℕ) (out : (ℕ → (Fin L → ℕ)) → ℝ)
    (hout : ∀ ω, out ω = 2 ^ (J ω) * (∑ s, ω (J ω) s : ℕ)) (jstar : ℕ) :
    (trajLaw θ).real {ω | ¬ ((1 - ε / 2) * Lval ≤ out ω ∧ out ω ≤ (1 + ε / 2) * Lval)}
      ≤ (∑ j ∈ Finset.range jstar, 2 * Real.exp (-(epsP ^ 2 * totalRate θ j / 3)))
        + (trajLaw θ).real {ω | jstar ≤ J ω} := by
  classical
  set Err : ℕ → Set (ℕ → (Fin L → ℕ)) := fun j =>
    {ω | ¬ ((1 - epsP) * totalRate θ j ≤ (∑ s, ω j s : ℕ) ∧
          ((∑ s, ω j s : ℕ) : ℝ) ≤ (1 + epsP) * totalRate θ j)} with hErr
  -- the covering
  have hsub : {ω | ¬ ((1 - ε / 2) * Lval ≤ out ω ∧ out ω ≤ (1 + ε / 2) * Lval)}
      ⊆ (⋃ j ∈ Finset.range jstar, Err j) ∪ {ω | jstar ≤ J ω} := by
    intro ω hω
    by_cases hJ : jstar ≤ J ω
    · exact Or.inr hJ
    rw [Nat.not_le] at hJ
    refine Or.inl (Set.mem_biUnion (Finset.mem_range.2 hJ) ?_)
    intro hgood
    obtain ⟨hg1, hg2⟩ := hgood
    -- `2^j · totalRate θ j = ∑ θ`
    have h2 : (2 : ℝ) ^ (J ω) * totalRate θ (J ω) = ∑ s, θ s := by
      rw [totalRate, mul_div_cancel₀]
      positivity
    have hpow : (0:ℝ) < 2 ^ (J ω) := by positivity
    refine hω ⟨?_, ?_⟩
    · rw [hout ω]
      refine hlo.trans ?_
      rw [← h2]
      calc (1 - epsP) * (2 ^ (J ω) * totalRate θ (J ω))
          = 2 ^ (J ω) * ((1 - epsP) * totalRate θ (J ω)) := by ring
        _ ≤ 2 ^ (J ω) * (∑ s, ω (J ω) s : ℕ) := by
            exact mul_le_mul_of_nonneg_left hg1 hpow.le
    · rw [hout ω]
      refine le_trans ?_ hhi
      rw [← h2]
      calc (2:ℝ) ^ (J ω) * (∑ s, ω (J ω) s : ℕ)
          ≤ 2 ^ (J ω) * ((1 + epsP) * totalRate θ (J ω)) :=
            mul_le_mul_of_nonneg_left hg2 hpow.le
        _ = (1 + epsP) * (2 ^ (J ω) * totalRate θ (J ω)) := by ring
  refine le_trans (measureReal_mono hsub) ?_
  refine le_trans (measureReal_union_le _ _) ?_
  gcongr
  refine le_trans (measureReal_biUnion_finset_le _ _) ?_
  exact Finset.sum_le_sum fun j _ => trajLaw_err_le hθ0 hθ hep0 hep1 j

/-- Reindexing the epochs downwards: with `lamStar` the *smallest* rate, epoch `t`
counted from the bottom has rate `lamStar·2ᵗ`. -/
theorem epoch_reindex {L : ℕ} (θ : Fin L → ℝ) (epsP : ℝ) (jstar : ℕ) :
    ∑ j ∈ Finset.range jstar, 2 * Real.exp (-(epsP ^ 2 * totalRate θ j / 3))
      = ∑ t ∈ Finset.range jstar,
          2 * Real.exp (-(epsP ^ 2 * totalRate θ (jstar - 1 - t) / 3)) :=
  (Finset.sum_range_reflect _ _).symm

/-- Counting epochs from the bottom: level `j*−1−t` has rate `lamStar·2ᵗ`. -/
theorem totalRate_reindex {L : ℕ} (θ : Fin L → ℝ) {jstar t : ℕ} (ht : t < jstar) :
    totalRate θ (jstar - 1 - t) = totalRate θ (jstar - 1) * 2 ^ t := by
  have hle : t ≤ jstar - 1 := Nat.le_sub_one_of_lt ht
  obtain ⟨a, ha⟩ : ∃ a, jstar - 1 = a + t := ⟨jstar - 1 - t, (Nat.sub_add_cancel hle).symm⟩
  have hat : jstar - 1 - t = a := by omega
  rw [hat, ha, totalRate, totalRate, pow_add]
  field_simp

/-- **`lem:numlattice`'s bound, proved.** For the run driven by the coupled
family, the failure probability is at most the paper's three-term expression —
the `Err` epochs summed from the bottom, plus the overflow that caps the level.
Nothing here is assumed: `hlo`/`hhi` come from `lem:lattice`, `hsmall` and
`hrate` are conditions on the parameters, and everything else is proved above. -/
theorem traj_numlattice_le {L : ℕ} {θ : Fin L → ℝ} {epsP ε Lval : ℝ}
    (hθ0 : ∀ i, 0 ≤ θ i) (hθ : 0 < ∑ i, θ i) (hep0 : 0 < epsP) (hep1 : epsP ≤ 1)
    (hlo : (1 - ε / 2) * Lval ≤ (1 - epsP) * (∑ s, θ s))
    (hhi : (1 + epsP) * (∑ s, θ s) ≤ (1 + ε / 2) * Lval)
    {pt : Fin L → Space n} (hpt : Function.Injective pt)
    {vol : ι → ℝ} {covered : Space n → ι → Bool} {mem : ι → Fin L → Bool}
    (hcov : ∀ s i, covered (pt s) i = mem i s) (P : Params) (ρ : ℤ)
    (l : List ι) (hall : ∀ s, (l.any fun i => mem i s) = true)
    (jstar : ℕ) (hj1 : 1 ≤ jstar)
    (hsmall : ∀ i ∈ l, ¬ (P.thresh / vol i ≤ (1 / 2 : ℝ) ^ (jstar - 1)))
    (hrate : 2 * totalRate θ (jstar - 1) ≤ P.thresh) :
    (trajLaw θ).real {ω | ¬ ((1 - ε / 2) * Lval ≤
          run P (trajOracles hpt vol covered mem ω) ρ l ∧
        run P (trajOracles hpt vol covered mem ω) ρ l ≤ (1 + ε / 2) * Lval)}
      ≤ (∑ t ∈ Finset.range jstar,
            2 * Real.exp (-(epsP ^ 2 * (totalRate θ (jstar - 1) * 2 ^ t) / 3)))
        + Real.exp (-(P.thresh / 6)) := by
  classical
  set J : (ℕ → (Fin L → ℕ)) → ℕ := fun ω =>
    (l.foldl (step P (trajOracles hpt vol covered mem ω) ρ)
      (⟨0, 0⟩ : SketchState n)).level with hJdef
  set Bad : Set (ℕ → (Fin L → ℕ)) := {ω | ¬ ∀ j s, ω (j + 1) s ≤ ω j s} with hBad
  set Err : ℕ → Set (ℕ → (Fin L → ℕ)) := fun j =>
    {ω | ¬ ((1 - epsP) * totalRate θ j ≤ (∑ s, ω j s : ℕ) ∧
          ((∑ s, ω j s : ℕ) : ℝ) ≤ (1 + epsP) * totalRate θ j)} with hErr
  set Ovf : Set (ℕ → (Fin L → ℕ)) := {ω | P.thresh ≤ (∑ s, ω (jstar - 1) s : ℕ)} with hOvf
  have hnull : (trajLaw θ).real Bad = 0 := by
    rw [Measure.real, MeasureTheory.ae_iff.1 (trajLaw_ae_nested θ), ENNReal.toReal_zero]
  -- the covering
  have hsub : {ω | ¬ ((1 - ε / 2) * Lval ≤
        run P (trajOracles hpt vol covered mem ω) ρ l ∧
      run P (trajOracles hpt vol covered mem ω) ρ l ≤ (1 + ε / 2) * Lval)}
      ⊆ Bad ∪ ((⋃ j ∈ Finset.range jstar, Err j) ∪ Ovf) := by
    intro ω hω
    by_cases hn : ∀ j s, ω (j + 1) s ≤ ω j s
    · refine Or.inr ?_
      have hrun := run_eq_traj (vol := vol) hpt hn hcov P ρ l hall
      by_cases hcap : jstar ≤ J ω
      · exact Or.inr (le_of_lt (level_cap_subset hpt hn hcov P ρ l jstar hj1 hsmall hcap))
      rw [Nat.not_le] at hcap
      refine Or.inl (Set.mem_biUnion (Finset.mem_range.2 hcap) ?_)
      rintro ⟨hg1, hg2⟩
      have h2 : (2 : ℝ) ^ (J ω) * totalRate θ (J ω) = ∑ s, θ s := by
        rw [totalRate, mul_div_cancel₀]; positivity
      have hpow : (0:ℝ) < 2 ^ (J ω) := by positivity
      refine hω ⟨?_, ?_⟩
      · rw [hrun]
        refine hlo.trans ?_
        rw [← h2]
        calc (1 - epsP) * (2 ^ (J ω) * totalRate θ (J ω))
            = 2 ^ (J ω) * ((1 - epsP) * totalRate θ (J ω)) := by ring
          _ ≤ 2 ^ (J ω) * (∑ s, ω (J ω) s : ℕ) := mul_le_mul_of_nonneg_left hg1 hpow.le
      · rw [hrun]
        refine le_trans ?_ hhi
        rw [← h2]
        calc (2:ℝ) ^ (J ω) * (∑ s, ω (J ω) s : ℕ)
            ≤ 2 ^ (J ω) * ((1 + epsP) * totalRate θ (J ω)) :=
              mul_le_mul_of_nonneg_left hg2 hpow.le
          _ = (1 + epsP) * (2 ^ (J ω) * totalRate θ (J ω)) := by ring
    · exact Or.inl hn
  refine le_trans (measureReal_mono hsub) ?_
  refine le_trans (measureReal_union_le _ _) ?_
  rw [hnull, zero_add]
  refine le_trans (measureReal_union_le _ _) ?_
  gcongr
  · refine le_trans (measureReal_biUnion_finset_le _ _) ?_
    refine le_trans (Finset.sum_le_sum fun j _ => trajLaw_err_le hθ0 hθ hep0 hep1 j) ?_
    rw [epoch_reindex]
    exact Finset.sum_le_sum fun t ht => by
      rw [totalRate_reindex θ (Finset.mem_range.1 ht)]
  · exact trajLaw_noise_le hθ0 hθ (jstar - 1) hrate

end Ttc

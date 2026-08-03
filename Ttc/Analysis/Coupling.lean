/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import Ttc.Analysis.SketchProcess
import Ttc.Model.Pseudocode

/-!
# The coupled level family

README finding 15: `lem:numlattice`'s `Err(j)` has to be an event about a level-`j`
process defined for **every** `j` on one probability space, and coupled to the run
so that the run's final state *is* the family at its own stopping level. The paper
never constructs it. This file does.

## The construction

Randomness: a level-`0` count `A s` for each lattice point, and a fair coin
`coin s e j` for each (point, rank, level). The family is then

```
famCount A coin s 0       = A s
famCount A coin s (j+1)   = #{e < famCount A coin s j | coin s e j}
```

**Why the coins are indexed by rank, not by original copy.** A thinning of a
multiset re-indexes the survivors — a multiset records multiplicities, not which
copy is which — so a family defined by "copy `e` of the original `A s` survives
iff its first `j` coins are heads" cannot be implemented by an oracle that sees
only counts. Indexing by *rank among the current survivors* makes the recursion
implementable from the count alone, which is exactly what `halve` gets to see,
while still being a nested fair thinning at every level.
-/

namespace Ttc

open MeasureTheory ProbabilityTheory

variable {L : ℕ}

/-- The coins: for each lattice point, each level, and each *current count* `k`, a
random subset of `Iio k` — the ranks that survive that thinning.

Indexing by the current count as well as the level is what makes the law
definitional: `ProbabilityTheory.binomial k p` **is** `setBer(Iio k, p).map ncard`
in Mathlib, so "how many survive" is binomial by construction. Only one `k` is
ever queried at a given `(s, j)` — the one the run actually reaches — and the
coins at distinct `(s, j)` are independent, which is what the induction needs. -/
abbrev Coins (L : ℕ) := Fin L → ℕ → ℕ → Set ℕ

/-- How many of `k` copies of `s` survive the level-`j` thinning. The intersection
with `Iio k` is a no-op almost surely (`setBernoulli_ae_subset`) and is there so
that `Ttc.survive_le` holds for *every* coin assignment, not just almost all. -/
noncomputable def survive (c : Coins L) (s : Fin L) (j k : ℕ) : ℕ :=
  (c s j k ∩ Set.Iio k).ncard

theorem survive_le (c : Coins L) (s : Fin L) (j k : ℕ) : survive c s j k ≤ k := by
  rw [survive]
  calc (c s j k ∩ Set.Iio k).ncard
      ≤ (Set.Iio k).ncard := Set.ncard_le_ncard Set.inter_subset_right (Set.finite_Iio k)
    _ = k := by simp [Set.Iio, Set.ncard_eq_toFinset_card']

@[simp] theorem survive_zero (c : Coins L) (s : Fin L) (j : ℕ) : survive c s j 0 = 0 := by
  have := survive_le c s j 0
  omega

/-- **The law of one thinning is binomial** — and definitionally so: Mathlib
*defines* `binomial k p` as `setBer(Iio k, p).map ncard`, and the intersection with
`Iio k` is almost surely the identity. -/
theorem map_survive (k : ℕ) :
    (setBernoulli (Set.Iio k) half).map (fun S => (S ∩ Set.Iio k).ncard)
      = binomial k half := by
  rw [binomial]
  refine Measure.map_congr ?_
  filter_upwards [setBernoulli_ae_subset (u := Set.Iio k) (p := half)] with S hS
  rw [Set.inter_eq_left.2 hS]

/-- **The coupled family.** `famCount A coin s j` is the number of copies of the
lattice point `s` present at level `j`. -/
noncomputable def famCount (A : Fin L → ℕ) (c : Coins L) (s : Fin L) : ℕ → ℕ
  | 0 => A s
  | j + 1 => survive c s j (famCount A c s j)

@[simp] theorem famCount_zero (A : Fin L → ℕ) (c : Coins L) (s : Fin L) :
    famCount A c s 0 = A s := rfl

@[simp] theorem famCount_succ (A : Fin L → ℕ) (c : Coins L) (s : Fin L) (j : ℕ) :
    famCount A c s (j + 1) = survive c s j (famCount A c s j) := rfl

/-- **The family is nested**: thinning only removes copies. -/
theorem famCount_succ_le (A : Fin L → ℕ) (c : Coins L) (s : Fin L) (j : ℕ) :
    famCount A c s (j + 1) ≤ famCount A c s j :=
  survive_le c s j _

/-- **The family is antitone in the level.** -/
theorem famCount_antitone (A : Fin L → ℕ) (c : Coins L) (s : Fin L) :
    Antitone (famCount A c s) := by
  refine antitone_nat_of_succ_le fun j => ?_
  exact famCount_succ_le A c s j

/-- Every level's count is bounded by the level-`0` count. -/
theorem famCount_le_zero (A : Fin L → ℕ) (c : Coins L) (s : Fin L) (j : ℕ) :
    famCount A c s j ≤ A s :=
  famCount_antitone A c s (Nat.zero_le j)

/-! ## The coupling space

The randomness of the whole family lives on one space: a level-`0` count per
lattice point, and the coins. Only the *coins* need an infinite product (over
levels and counts), which `MeasureTheory.Measure.infinitePi` supplies — the same
construction `setBernoulli` itself is built from.
-/

/-- The law of the coins: independent across points, levels and counts. -/
noncomputable def coinLaw (L : ℕ) : Measure (Coins L) :=
  Measure.pi fun _ : Fin L =>
    Measure.infinitePi fun _ : ℕ => Measure.infinitePi fun k : ℕ => setBernoulli (Set.Iio k) half

instance isProbabilityMeasure_coinLaw (L : ℕ) : IsProbabilityMeasure (coinLaw L) := by
  rw [coinLaw]; infer_instance

/-- **The coupling space**: the level-`0` counts together with the coins. Every
level of the family is a function of a single point of this space, which is what
makes the family *coupled* rather than a collection of unrelated marginals. -/
noncomputable def famLaw (θ : Fin L → ℝ) : Measure ((Fin L → ℕ) × Coins L) :=
  (Measure.pi fun s => poissonMeasure (θ s).toNNReal).prod (coinLaw L)

instance isProbabilityMeasure_famLaw (θ : Fin L → ℝ) :
    IsProbabilityMeasure (famLaw θ) := by
  rw [famLaw]; infer_instance

/-- The family, as a random vector on the coupling space. -/
noncomputable def famVec (j : ℕ) (ω : (Fin L → ℕ) × Coins L) : Fin L → ℕ :=
  fun s => famCount ω.1 ω.2 s j

@[simp] theorem famVec_zero (ω : (Fin L → ℕ) × Coins L) : famVec 0 ω = ω.1 := rfl

/-- **Level `0` of the family has the level-`0` law.** The base case of the
induction identifying every level with `Ttc.levelLaw`. -/
theorem map_famVec_zero (θ : Fin L → ℝ) :
    (famLaw θ).map (famVec 0) = levelLaw θ 0 := by
  have hfst : (famLaw θ).map Prod.fst = Measure.pi fun s => poissonMeasure (θ s).toNNReal := by
    rw [famLaw, Measure.map_fst_prod, measure_univ, one_smul]
  have hvec : (famVec (L := L) 0) = Prod.fst := by
    funext ω; exact famVec_zero ω
  rw [hvec, hfst, levelLaw]
  congr 1
  funext s
  congr 2
  simp

/-! ## The thinning kernel

The coupled family is a Markov chain on count vectors: level `j+1` is level `j`
thinned. Packaging one step as a `ProbabilityTheory.Kernel` is what lets Mathlib's
Ionescu–Tulcea construction (`ProbabilityTheory.Kernel.traj`) build the *whole
trajectory* on one space — which is precisely the coupled family finding 15 needs,
with every level's marginal coming from `Ttc.chainLaw_eq_levelLaw` rather than
from an independence argument about product coordinates.
-/

/-- **One thinning step, as a Markov kernel.** Each coordinate is thinned
`Binomial(·, ½)`, independently across lattice points. -/
noncomputable def thinKernel (L : ℕ) : Kernel (Fin L → ℕ) (Fin L → ℕ) where
  toFun k := Measure.pi fun s => binomial (k s) half
  measurable' := Measurable.of_discrete

@[simp] theorem thinKernel_apply (L : ℕ) (k : Fin L → ℕ) :
    thinKernel L k = Measure.pi fun s => binomial (k s) half := rfl

instance isMarkovKernel_thinKernel (L : ℕ) : IsMarkovKernel (thinKernel L) :=
  ⟨fun k => by rw [thinKernel_apply]; infer_instance⟩

/-- **The chain step, in kernel form**: binding a product of Poissons through the
thinning kernel halves every rate. This is `Ttc.pi_poisson_bind_binomial_half`
read as a kernel composition, and it is the transition `Ttc.chainLaw` iterates. -/
theorem bind_thinKernel {θ : Fin L → ℝ} (hθ : ∀ i, 0 ≤ θ i) :
    (Measure.pi fun i => poissonMeasure (θ i).toNNReal).bind (thinKernel L)
      = Measure.pi fun i => poissonMeasure (θ i / 2).toNNReal := by
  have hfun : (⇑(thinKernel L)) = fun k => Measure.pi fun i => binomial (k i) half := rfl
  rw [hfun]
  exact pi_poisson_bind_binomial_half hθ

/-- **Every level of the chain is the level law** — restated over the kernel, so
that the trajectory construction inherits it. -/
theorem chainLaw_eq_levelLaw' {θ : Fin L → ℝ} (hθ : ∀ i, 0 ≤ θ i) (j : ℕ) :
    chainLaw θ j = levelLaw θ j := chainLaw_eq_levelLaw hθ j

/-! ## The trajectory: the coupled family on one space

`ProbabilityTheory.Kernel.trajMeasure` (Ionescu–Tulcea) turns the one-step
thinning kernel into the law of the **whole trajectory** `ℕ → (Fin L → ℕ)`. That
is the object README finding 15 says the paper needs and never builds: every level
lives on the same sample point, so `Err(j)` is an unconditional event for every
`j`, and the run can be identified with the family at its own stopping level.
-/

/-- The chain's kernel at step `n`: thin the state at time `n`. The history is
available but only its last coordinate is read — the chain is Markov. -/
noncomputable def chainKernel (L n : ℕ) :
    Kernel ((_i : ↥(Finset.Iic n)) → (Fin L → ℕ)) (Fin L → ℕ) :=
  Kernel.comap (thinKernel L) (fun h => h ⟨n, Finset.mem_Iic.2 le_rfl⟩) (measurable_pi_apply _)

instance isMarkovKernel_chainKernel (L n : ℕ) : IsMarkovKernel (chainKernel L n) := by
  rw [chainKernel]; infer_instance

/-- **The coupled family, as one measure on trajectories.** Start from the
level-`0` product of Poissons and thin forever. -/
noncomputable def trajLaw (θ : Fin L → ℝ) : Measure (ℕ → (Fin L → ℕ)) :=
  Kernel.trajMeasure (Measure.pi fun s => poissonMeasure (θ s).toNNReal) (chainKernel L)

instance isProbabilityMeasure_trajLaw (θ : Fin L → ℝ) :
    IsProbabilityMeasure (trajLaw θ) := by
  rw [trajLaw]; infer_instance

/-- Composing with a `comap`ped kernel is composing after mapping. -/
theorem bind_comap {α β γ : Type*} [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpace γ]
    (κ : Kernel α γ) [IsSFiniteKernel κ] {f : β → α} (hf : Measurable f)
    (ν : Measure β) [SFinite ν] :
    ν.bind (Kernel.comap κ f hf) = (ν.map f).bind κ := by
  ext s hs
  rw [Measure.bind_apply hs (Kernel.comap κ f hf).aemeasurable,
    Measure.bind_apply hs κ.aemeasurable,
    lintegral_map (κ.measurable_coe hs) hf]
  rfl

/-- **The trajectory's step**: the marginal at level `a+1` is the marginal at
level `a` pushed through the thinning kernel.

Read off the joint law of (history up to `a`, state at `a+1`), take its second
marginal, then use that `Ttc.chainKernel` consults only the last coordinate of the
history — so the history marginal collapses to the level-`a` marginal. -/
theorem map_trajLaw_step (θ : Fin L → ℝ) (a : ℕ) :
    (trajLaw θ).map (fun ω => ω (a + 1))
      = ((trajLaw θ).map (fun ω => ω a)).bind (thinKernel L) := by
  set μ₀ : Measure (Fin L → ℕ) := Measure.pi fun s => poissonMeasure (θ s).toNNReal with hμ₀
  have hjoint := Kernel.map_frestrictLe_trajMeasure_compProd_eq_map_trajMeasure
    (X := fun _ : ℕ => (Fin L → ℕ)) (μ₀ := μ₀) (κ := chainKernel L) (a := a)
  have hsnd := congrArg Measure.snd hjoint
  -- the left side is a composition with the kernel
  rw [Measure.snd_compProd] at hsnd
  -- the right side is the marginal at `a+1`
  rw [Measure.snd, Measure.map_map (by fun_prop) (by fun_prop)] at hsnd
  -- drop the history down to the coordinate the kernel reads
  rw [chainKernel, bind_comap, Measure.map_map (measurable_pi_apply _) (by fun_prop)] at hsnd
  simp only [Function.comp_def, Preorder.frestrictLe_apply] at hsnd
  rw [trajLaw, ← hsnd]

/-- **Level `0` of the trajectory is the level-`0` law.** The coordinates up to
time `0` of `Kernel.traj κ 0` are deterministic, so the initial distribution
passes straight through. -/
theorem map_trajLaw_zero (θ : Fin L → ℝ) :
    (trajLaw θ).map (fun ω => ω 0) = Measure.pi fun s => poissonMeasure (θ s).toNNReal := by
  have hdet := Kernel.traj_map_frestrictLe_of_le (X := fun _ : ℕ => (Fin L → ℕ))
    (κ := chainKernel L) (a := 0) (b := 0) le_rfl
  have hmap : Kernel.map (Kernel.traj (X := fun _ : ℕ => (Fin L → ℕ)) (chainKernel L) 0)
        (fun x => x 0)
      = Kernel.deterministic
          (fun x : (_i : ↥(Finset.Iic 0)) → (Fin L → ℕ) => x ⟨0, Finset.mem_Iic.2 le_rfl⟩)
          (measurable_pi_apply _) := by
    rw [show (fun x : ℕ → (Fin L → ℕ) => x 0)
        = (fun h : (_i : ↥(Finset.Iic 0)) → (Fin L → ℕ) => h ⟨0, Finset.mem_Iic.2 le_rfl⟩)
          ∘ (Preorder.frestrictLe 0) from rfl,
      Kernel.map_comp_right _ (Preorder.measurable_frestrictLe 0) (measurable_pi_apply _), hdet,
      Kernel.deterministic_map _ (measurable_pi_apply _)]
    rfl
  rw [trajLaw, Kernel.trajMeasure, Measure.map_comp _ _ (by fun_prop), hmap,
    Measure.deterministic_comp_eq_map, Measure.map_map (by fun_prop) (by fun_prop)]
  simp [Function.comp_def]

/-- **Every level of the trajectory carries the level law.** The coupled family of
README finding 15 exists, and its marginals are exactly the laws the `Err` and
`Noise` estimates were proved over. -/
theorem map_trajLaw_eval {θ : Fin L → ℝ} (hθ : ∀ s, 0 ≤ θ s) (j : ℕ) :
    (trajLaw θ).map (fun ω => ω j) = levelLaw θ j := by
  induction j with
  | zero =>
      rw [map_trajLaw_zero, levelLaw]
      congr 1
      funext s
      congr 2
      simp
  | succ a ih =>
      rw [map_trajLaw_step, ih, levelLaw]
      have hrate : ∀ s, (0:ℝ) ≤ θ s / 2 ^ a := fun s => by have := hθ s; positivity
      have h := bind_thinKernel (θ := fun s => θ s / 2 ^ a) hrate
      rw [levelLaw] at *
      rw [h]
      congr 1
      funext s
      congr 2
      rw [pow_succ]
      ring

/-! ## Count vectors as multisets

The run's state is a `Multiset (Space n)`; the family is a count vector. This is
the dictionary between them, given an injective enumeration `pt` of the lattice
points. `Ttc.toMultiset` builds the multiset with prescribed multiplicities, and
`Ttc.count_toMultiset` says it has exactly those multiplicities — which is what
lets the oracles of step 3 *read* the family.
-/

/-- The multiset holding `k s` copies of the lattice point `pt s`. -/
noncomputable def toMultiset {n : ℕ} (pt : Fin L → Space n) (k : Fin L → ℕ) :
    Multiset (Space n) :=
  ∑ s, Multiset.replicate (k s) (pt s)

@[simp] theorem card_toMultiset {n : ℕ} (pt : Fin L → Space n) (k : Fin L → ℕ) :
    Multiset.card (toMultiset pt k) = ∑ s, k s := by
  rw [toMultiset, Multiset.card_sum]
  exact Finset.sum_congr rfl fun s _ => Multiset.card_replicate _ _

/-- **The multiplicities are the ones prescribed** — the point of the dictionary.
Needs `pt` injective, so that distinct indices contribute to distinct points. -/
theorem count_toMultiset {n : ℕ} {pt : Fin L → Space n} (hpt : Function.Injective pt)
    (k : Fin L → ℕ) (s : Fin L) :
    Multiset.count (pt s) (toMultiset pt k) = k s := by
  classical
  rw [toMultiset, Multiset.count_sum']
  rw [Finset.sum_eq_single s]
  · rw [Multiset.count_replicate_self]
  · intro t _ hts
    rw [Multiset.count_replicate, if_neg (fun h => hts (hpt h))]
  · intro h
    exact absurd (Finset.mem_univ s) h

/-- Points outside the enumeration do not occur. -/
theorem count_toMultiset_of_notMem {n : ℕ} (pt : Fin L → Space n) (k : Fin L → ℕ)
    {x : Space n} (hx : ∀ s, pt s ≠ x) :
    Multiset.count x (toMultiset pt k) = 0 := by
  classical
  rw [toMultiset, Multiset.count_sum']
  refine Finset.sum_eq_zero fun t _ => ?_
  rw [Multiset.count_replicate, if_neg (hx t)]

/-- **Fewer copies means a sub-multiset** — what `Oracles.halve_le` needs of a
thinning that reads the family. -/
theorem toMultiset_le {n : ℕ} {pt : Fin L → Space n} (hpt : Function.Injective pt)
    {k k' : Fin L → ℕ} (h : ∀ s, k' s ≤ k s) :
    toMultiset pt k' ≤ toMultiset pt k := by
  classical
  rw [Multiset.le_iff_count]
  intro x
  by_cases hx : ∃ s, pt s = x
  · obtain ⟨s, rfl⟩ := hx
    rw [count_toMultiset hpt, count_toMultiset hpt]
    exact h s
  · simp only [not_exists] at hx
    rw [count_toMultiset_of_notMem pt k' hx, count_toMultiset_of_notMem pt k hx]

/-- **A count-bounded multiset is a sub-multiset** — the form `Oracles.halve_le`
needs, where the ambient multiset is arbitrary rather than another `toMultiset`. -/
theorem toMultiset_le_of_count_le {n : ℕ} {pt : Fin L → Space n}
    (hpt : Function.Injective pt) {k : Fin L → ℕ} {X : Multiset (Space n)}
    (h : ∀ s, k s ≤ Multiset.count (pt s) X) :
    toMultiset pt k ≤ X := by
  classical
  rw [Multiset.le_iff_count]
  intro x
  by_cases hx : ∃ s, pt s = x
  · obtain ⟨s, rfl⟩ := hx
    rw [count_toMultiset hpt]
    exact h s
  · simp only [not_exists] at hx
    rw [count_toMultiset_of_notMem pt k hx]
    exact Nat.zero_le _

/-! ## The oracles that read the trajectory

This is the coupling made concrete: the run's randomness *is* the family. `halve`
returns the family's next level (capped at what the state actually holds, so that
`halve_le` holds for every multiset, not just the ones the run produces); `pois`
returns the family's total over the cube; `gen` returns the family restricted to
the cube.

`gen` has to return exactly `N` points for **every** `N` (`Oracles.gen_card`), but
the family's size is whatever `pois` returned. So `gen` falls back to a filler of
the right size when the two disagree — a branch the run never takes, since it
always passes `gen` the `N` that `pois` produced. The filler is drawn from the
cube's own lattice points where it has any, so that the membership contract still
holds; see `Ttc.padPoint`.
-/

/-- A lattice point of cube `i`, if it has one. Used only for `gen`'s
never-taken filler branch. -/
noncomputable def padPoint {n : ℕ} {ι : Type*} (pt : Fin L → Space n) (mem : ι → Fin L → Bool)
    (i : ι) : Space n :=
  open Classical in
  if h : ∃ s, mem i s = true then pt h.choose else 0

/-- **The oracle bundle that reads a trajectory.** -/
noncomputable def trajOracles {n : ℕ} {ι : Type*} {pt : Fin L → Space n}
    (hpt : Function.Injective pt)
    (vol : ι → ℝ) (covered : Space n → ι → Bool) (mem : ι → Fin L → Bool)
    (ω : ℕ → (Fin L → ℕ)) : Oracles n ι where
  vol := vol
  covered := covered
  halve := fun _c j X =>
    toMultiset pt fun s => min (ω (j + 1) s) (Multiset.count (pt s) X)
  halve_le := fun _c j X =>
    toMultiset_le_of_count_le hpt fun s => min_le_right _ _
  pois := fun _c i j _lam => ∑ s ∈ Finset.univ.filter fun s => mem i s = true, ω j s
  gen := fun _c i j N _ρ =>
    open Classical in
    if Multiset.card (toMultiset pt fun s => if mem i s then ω j s else 0) = N then
      toMultiset pt fun s => if mem i s then ω j s else 0
    else Multiset.replicate N (padPoint pt mem i)
  gen_card := by
    intro _c i j N _ρ
    classical
    by_cases h : Multiset.card (toMultiset pt fun s => if mem i s then ω j s else 0) = N
    · simp only [h, if_pos]
    · simp only [h, if_false]
      exact Multiset.card_replicate _ _

end Ttc

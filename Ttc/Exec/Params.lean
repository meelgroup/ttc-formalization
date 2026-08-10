import Ttc.Model.Pseudocode
import Ttc.Lattice.Decomposition

/-!
# The parameter block, computed from the algorithm's inputs

`Ttc.TtcProb` carries `P : Params` as a **field**, together with four fields tying
it back to the run — `eps_eq`, `delta_eq`, `dim_eq`, and the two bounds
`cubes_le`, `facets_le`.  So the parameter block that `alg:ttc` lines 12–20
*computes* is currently *assumed*.

This file removes that gap.  `Ttc.ttcParams` — which lives in `Model/Pseudocode`,
with the rest of the algorithm — builds the block from exactly the data the
algorithm has: the DNF it enumerates, the dimension, and the requested `(ε, δ)`.
The lemmas below discharge all five tie-back fields, four of them by `rfl` and the
two bounds by `le_refl`.

This is step 4 of the capstone restatement (`END-TO-END-PLAN.md`, *The endgoal*),
mirroring `ApproxNFA.countNFAParams` (`nfalean/ApproxNFA/Algorithm/Faithful.lean`),
which likewise computes the whole block from `(A, n, ε, δ)` alone.

**What is genuinely an input condition, and what is not.**  `Params` demands
`1 ≤ m` and `1 ≤ r`: at least one cube, and at least one facet.  Neither is
derivable from nothing — an unsatisfiable `φ` has an empty DNF — so they are
carried as hypotheses of `ttcParams` rather than manufactured.  They are, however,
*visible* hypotheses about the input, which is exactly the difference the
restatement is about.  `Ttc.one_le_card_cubes` and `Ttc.one_le_card_facets`
(below) reduce them to the two honest statements "the DNF has a cube" and "that
cube has a literal".

`Params.m` is `ℕ` while `Params.r` is `ℝ`; the two bounds are therefore stated with
a cast on each side, matching `Ttc.TtcProb.cubes_le` / `facets_le` verbatim.
-/

namespace Ttc

variable {A : Type*}

/-! ## Where the block and its side conditions live

`Ttc.ttcParams`, its total form `Ttc.ttcParamsTotal`, the fallback `Ttc.junkParams`
and the two `Finite` instances (`Ttc.instFiniteCubeMem`, `Ttc.instFiniteFacetIndex`)
are in `Model/`: the block is part of the algorithm, and `Ttc.ttcParamsTotal` — the
form the run actually reads — is in the definitional closure of `Ttc.ttc`.

Everything that is only ever used to *supply* `Ttc.ttcParams`' five proof arguments,
or that is only ever proved *about* the block, is here.  None of it is in that
closure, nor in the closure of `Ttc.ttc_volume_estimate`'s statement, so none of it
belongs in the audit surface — `Ttc/Audit/ClosureCheck.lean` is what measures that.

## `hm` and `hr`, derived rather than assumed

`hm` comes from the DNF being nonempty; `hr` from the solution set being bounded.
Neither is derivable from nothing — an unsatisfiable `φ` has an empty DNF, and
`φ = tt` has the single literal-free cube `[]` — so each is derived from a
hypothesis the top-level statement already carries.
-/

/-- **The DNF has a cube ⟹ `1 ≤ m`.**  Reduces `Params`' `hm` to a statement about
the input formula's decomposition. -/
theorem one_le_card_cubes {D : DNF A} {c : Cube A} (hc : c ∈ D) :
    1 ≤ Nat.card {c : Cube A // c ∈ D} :=
  Nat.one_le_iff_ne_zero.mpr <| Nat.card_ne_zero.mpr ⟨⟨⟨c, hc⟩⟩, inferInstance⟩

/-- **Some cube has a literal ⟹ `1 ≤ r`.**  Reduces `Params`' `hr` likewise.  A cube
with no literals is the empty conjunction, whose region is all of `Space n`; the
facet count is then genuinely `0` and `Params` genuinely does not apply. -/
theorem one_le_card_facets {D : DNF A} {c : Cube A} (hc : c ∈ D) {l : Lit A}
    (hl : l ∈ c) : 1 ≤ Nat.card (FacetIndex D) :=
  Nat.one_le_iff_ne_zero.mpr <| Nat.card_ne_zero.mpr ⟨⟨⟨⟨c, hc⟩, ⟨l, hl⟩⟩⟩, inferInstance⟩

/-- A cube with no literals denotes all of the ambient space: `Cube.holds` is a
bounded universal quantifier over the cube's literals, hence vacuously true. -/
theorem region_nil {X : Type*} {M : A → Set X} : region M ([] : Cube A) = Set.univ :=
  Set.eq_univ_of_forall fun _ _ h => absurd h (List.not_mem_nil)

/-- `ℝⁿ` is unbounded as soon as `1 ≤ n`.  Used to contradict `hbdd` in
`Ttc.exists_lit_of_isBounded`. -/
theorem not_isBounded_univ_space {n : ℕ} (hn : 1 ≤ n) :
    ¬ Bornology.IsBounded (Set.univ : Set (Space n)) := by
  haveI : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  haveI : Nontrivial (Space n) := inferInstance
  exact NormedSpace.unbounded_univ ℝ (Space n)

/-- **Every cube of a DNF of a formula with bounded solution set has a literal.**

If some cube `c` were literal-free then `region M c = Set.univ`, and soundness of
the decomposition (`Ttc.region_subset_sol`) would give `Set.univ ⊆ sol M φ`,
making `sol M φ` unbounded — contradicting `hbdd`.  This is what discharges
`Ttc.ttcParams`' `hr` without assuming it. -/
theorem exists_lit_of_isBounded {n : ℕ} (hn : 1 ≤ n)
    {M : A → Set (Space n)} {φ : BForm A} {D : DNF A}
    (hD : IsDNFOf D φ) (hbdd : Bornology.IsBounded (sol M φ))
    {c : Cube A} (hc : c ∈ D) : ∃ l : Lit A, l ∈ c := by
  by_contra hno
  have hcnil : c = [] :=
    List.eq_nil_iff_forall_not_mem.mpr fun l hl => hno ⟨l, hl⟩
  subst hcnil
  have huniv : (Set.univ : Set (Space n)) ⊆ sol M φ := by
    rw [← region_nil (M := M) (A := A)]
    exact region_subset_sol hD hc
  exact not_isBounded_univ_space hn (hbdd.subset huniv)

/-- **A nonempty DNF has at least one cube**, in the `Nat.card` form
`Ttc.ttcParams` wants for its `hm`. -/
theorem one_le_card_cubes_of_ne_nil {D : DNF A} (hne : D ≠ []) :
    1 ≤ Nat.card {c : Cube A // c ∈ D} := by
  obtain ⟨c, hc⟩ := List.exists_mem_of_ne_nil D hne
  exact one_le_card_cubes hc

/-- **`hr`, from boundedness of the solution set.**  Combines
`Ttc.exists_lit_of_isBounded` with `Ttc.one_le_card_facets`.  Stated for an
arbitrary DNF `D` of `φ`, so that it applies to deduplicated variants of
`Ttc.toDNF φ` as well. -/
theorem one_le_card_facets_of_isBounded {n : ℕ} (hn : 1 ≤ n)
    {M : A → Set (Space n)} {φ : BForm A} {D : DNF A}
    (hD : IsDNFOf D φ) (hbdd : Bornology.IsBounded (sol M φ)) (hne : D ≠ []) :
    1 ≤ Nat.card (FacetIndex D) := by
  obtain ⟨c, hc⟩ := List.exists_mem_of_ne_nil D hne
  obtain ⟨l, hl⟩ := exists_lit_of_isBounded hn hD hbdd hc
  exact one_le_card_facets hc hl

/-! ## The totalisation's agreement lemmas

`Ttc.ttcParamsTotal` (`Model/Pseudocode`) **decides** the five side conditions
classically and falls back on `Ttc.junkParams` when they fail, which is what lets
`Ttc.ttcAlgOutput` and `Ttc.ttcRun` carry no proof binder.  These two lemmas are
what makes that honest: the block is `Ttc.ttcParams` exactly where the headline's
hypotheses hold, and the junk value elsewhere.  Neither is in the closure of
`Ttc.ttc` — the *definition* needs no lemma — so both are here. -/

/-- **The agreement lemma — the whole point.**  Where the five side conditions hold,
the total block *is* `Ttc.ttcParams` at the very same arguments.  The proofs
`hε0 … hr` occur on the right and not on the left, and by proof irrelevance the
right-hand side does not depend on which proofs they are; so every theorem stated
about `Ttc.ttcParams` transfers verbatim. -/
theorem ttcParamsTotal_eq (D : DNF A) (n : ℕ) (ε δ : ℝ)
    (hε0 : 0 < ε) (hε1 : ε ≤ 1) (hn : 1 ≤ n)
    (hm : 1 ≤ Nat.card {c : Cube A // c ∈ D}) (hr : 1 ≤ Nat.card (FacetIndex D)) :
    ttcParamsTotal D n ε δ = ttcParams D n ε δ hε0 hε1 hn hm hr := by
  rw [ttcParamsTotal, dif_pos ⟨hε0, hε1, hn, hm, hr⟩]

/-- **The junk branch, named.**  Stated so that the fallback is visible as a
statement rather than only as a branch of the `dite`: if any side condition fails
the block is the default value, and in particular nothing about the formula can be
read off it. -/
theorem ttcParamsTotal_eq_junk (D : DNF A) (n : ℕ) (ε δ : ℝ)
    (h : ¬ (0 < ε ∧ ε ≤ 1 ∧ 1 ≤ n ∧ 1 ≤ Nat.card {c : Cube A // c ∈ D} ∧
      1 ≤ Nat.card (FacetIndex D))) :
    ttcParamsTotal D n ε δ = junkParams := by
  rw [ttcParamsTotal, dif_neg h]

/-! ## What is proved *about* the block

The tie-back lemmas below are what `Ttc.TtcProb`'s five fields become once the block
is computed rather than assumed.
-/

variable (D : DNF A) (n : ℕ) (ε δ : ℝ) (hε0 : 0 < ε) (hε1 : ε ≤ 1) (hn : 1 ≤ n)
  (hm : 1 ≤ Nat.card {c : Cube A // c ∈ D}) (hr : 1 ≤ Nat.card (FacetIndex D))

/-! ## The five tie-back fields, discharged

These are, verbatim, `Ttc.TtcProb.eps_eq`, `delta_eq`, `dim_eq`, `cubes_le` and
`facets_le` instantiated at `P := ttcParams …`.  Four hold by `rfl`; the two bounds
hold by `le_refl` because the block stores the counts exactly.
-/

@[simp] theorem ttcParams_eps : (ttcParams D n ε δ hε0 hε1 hn hm hr).ε = ε := rfl

@[simp] theorem ttcParams_delta : (ttcParams D n ε δ hε0 hε1 hn hm hr).δ = δ := rfl

@[simp] theorem ttcParams_dim : (ttcParams D n ε δ hε0 hε1 hn hm hr).n = n := rfl

@[simp] theorem ttcParams_m :
    (ttcParams D n ε δ hε0 hε1 hn hm hr).m = Nat.card {c : Cube A // c ∈ D} := rfl

@[simp] theorem ttcParams_r :
    (ttcParams D n ε δ hε0 hε1 hn hm hr).r = (Nat.card (FacetIndex D) : ℝ) := rfl

/-- `Ttc.TtcProb.cubes_le`, discharged. -/
theorem ttcParams_cubes_le :
    (Nat.card {c : Cube A // c ∈ D} : ℝ) ≤ ((ttcParams D n ε δ hε0 hε1 hn hm hr).m : ℝ) :=
  le_of_eq (by rw [ttcParams_m])

/-- `Ttc.TtcProb.facets_le`, discharged. -/
theorem ttcParams_facets_le :
    (Nat.card (FacetIndex D) : ℝ) ≤ (ttcParams D n ε δ hε0 hε1 hn hm hr).r :=
  le_of_eq (by rw [ttcParams_r])

/-! ## The derived quantities are the paper's, on the computed block

Spot-checks that the block feeds `alg:ttc`'s own formulas.  They are `rfl`, but
stating them is what makes the transcription auditable without unfolding
`ttcParams`. -/

@[simp] theorem ttcParams_eta : (ttcParams D n ε δ hε0 hε1 hn hm hr).eta = ε / 8 := rfl

@[simp] theorem ttcParams_epsPrime :
    (ttcParams D n ε δ hε0 hε1 hn hm hr).epsPrime = ε / 12 := rfl

@[simp] theorem ttcParams_deltaPrime :
    (ttcParams D n ε δ hε0 hε1 hn hm hr).deltaPrime
      = δ / (4 * (Nat.card {c : Cube A // c ∈ D} : ℝ)) := rfl

end Ttc

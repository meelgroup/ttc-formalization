import Ttc.Model.Prelude

/-!
# The parameter block, computed from the algorithm's inputs

`Ttc.TtcProb` carries `P : Params` as a **field**, together with four fields tying
it back to the run — `eps_eq`, `delta_eq`, `dim_eq`, and the two bounds
`cubes_le`, `facets_le`.  So the parameter block that `alg:ttc` lines 12–20
*computes* is currently *assumed*.

This file removes that gap: `Ttc.ttcParams` builds the block from exactly the data
the algorithm has — the DNF it enumerates, the dimension, and the requested
`(ε, δ)` — and the lemmas below discharge all five tie-back fields, four of them by
`rfl` and the two bounds by `le_refl`.

This is step 4 of the capstone restatement (`END-TO-END-PLAN.md`, *The endgoal*),
mirroring `ApproxNFA.countNFAParams` (`nfalean/ApproxNFA/Algorithm/Faithful.lean`),
which likewise computes the whole block from `(A, n, ε, δ)` alone.

**What is genuinely an input condition, and what is not.**  `Params` demands
`1 ≤ m` and `1 ≤ r`: at least one cube, and at least one facet.  Neither is
derivable from nothing — an unsatisfiable `φ` has an empty DNF — so they are
carried as hypotheses of `ttcParams` rather than manufactured.  They are, however,
*visible* hypotheses about the input, which is exactly the difference the
restatement is about.  `Ttc.one_le_card_cubes` and `Ttc.one_le_card_facets` below
reduce them to the two honest statements "the DNF has a cube" and "that cube has a
literal".

`Params.m` is `ℕ` while `Params.r` is `ℝ`; the two bounds are therefore stated with
a cast on each side, matching `Ttc.TtcProb.cubes_le` / `facets_le` verbatim.
-/

namespace Ttc

variable {A : Type*}

/-! ## Finiteness of the two index types

Both are subtypes cut out by membership in a `List`, hence finite; `Nat.card` of an
infinite type is `0`, so the positivity lemmas below would be *false* without this.
-/

instance instFiniteCubeMem (D : DNF A) : Finite {c : Cube A // c ∈ D} :=
  List.finite_toSet D |>.to_subtype

instance instFiniteFacetIndex (D : DNF A) : Finite (FacetIndex D) := by
  unfold FacetIndex
  have : ∀ c : {c : Cube A // c ∈ D}, Finite {l : Lit A // l ∈ c.val} := fun c =>
    (List.finite_toSet c.val).to_subtype
  infer_instance

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

/-! ## The block itself -/

/-- **The parameter block `TTC(F, ε, δ)` computes**, from the DNF its AllSAT call
returned, the ambient dimension, and the requested accuracy and confidence.

`m` and `r` are the *exact* counts, not bounds: `alg:ttc` reads them off the
decomposition.  Taking them exactly is what makes `cubes_le` and `facets_le`
`le_refl` rather than assumptions.

Everything downstream — `η = ε/8`, `ε' = ε/12`, `δ' = δ/(4m)`, `Thresh`, `κ`, `γ`,
`ρ = ⌈log₁₀(γ/γ̂)⌉` — is already a `def` on `Params` (`Model/Prelude.lean`), so no
further computation is needed here. -/
noncomputable def ttcParams (D : DNF A) (n : ℕ) (ε δ : ℝ)
    (hε0 : 0 < ε) (hε1 : ε ≤ 1) (hn : 1 ≤ n)
    (hm : 1 ≤ Nat.card {c : Cube A // c ∈ D})
    (hr : 1 ≤ Nat.card (FacetIndex D)) : Params where
  ε := ε
  δ := δ
  n := n
  m := Nat.card {c : Cube A // c ∈ D}
  r := (Nat.card (FacetIndex D) : ℝ)
  hε0 := hε0
  hε1 := hε1
  hn := hn
  hm := hm
  hr := by exact_mod_cast hr

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

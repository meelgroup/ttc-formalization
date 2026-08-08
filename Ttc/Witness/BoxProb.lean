/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import Ttc.Witness.Box
import Ttc.Coupling.Transfer

/-!
# A non-degenerate witness

The development's original witness (`trivialProb`) inhabited `Ttc.TtcProb`
degenerately: empty DNF, `Sol(F) = ∅`, `L = 0`, so the failure event was empty and
every estimate held vacuously. CLAUDE.md §11 asks for better, and
`Ttc.numlattice_union_of_traj` makes better possible — a witness whose failure
bound is *proved*, not sidestepped. `trivialProb` has since been removed outright:
once `Ttc.TtcProb` carries the sampler fields, `D = []` forces `Lidx = 0` and
contradicts `big` (which forces `∑θ > 0`), so no degenerate instance exists
at all.

The instance is the box `[0,c]ⁿ` of `Witness/Box`, sampled by the coupled
family of `Coupling/Family`. The one real constraint is that the estimate is
only meaningful when the count clears the threshold, so the side `c` is chosen
from `Thresh` — which `Ttc.normalisedCount_box_ge` permits, since its bound
`cⁿ ≤ L` holds at every precision `ρ` and so does not depend on `ρ` being fixed
first.
-/

namespace Ttc

namespace Box

open MeasureTheory Pointwise

/-! ## Enumerating a finite set of points -/

variable {n : ℕ}

/-- The size of a finite point set. -/
noncomputable def size {S : Set (Space n)} (hS : S.Finite) : ℕ := hS.toFinset.card

/-- Its `i`-th point. -/
noncomputable def ptAt {S : Set (Space n)} (hS : S.Finite) (i : Fin (size hS)) : Space n :=
  (hS.toFinset.equivFin.symm i).val

theorem ptAt_mem {S : Set (Space n)} (hS : S.Finite) (i : Fin (size hS)) : ptAt hS i ∈ S :=
  hS.mem_toFinset.1 (hS.toFinset.equivFin.symm i).property

theorem ptAt_injective {S : Set (Space n)} (hS : S.Finite) :
    Function.Injective (ptAt hS) := fun _ _ h =>
  hS.toFinset.equivFin.symm.injective (Subtype.ext h)

/-- The enumeration is onto. -/
theorem exists_ptAt {S : Set (Space n)} (hS : S.Finite) {x : Space n} (hx : x ∈ S) :
    ∃ i, ptAt hS i = x := by
  refine ⟨hS.toFinset.equivFin ⟨x, hS.mem_toFinset.2 hx⟩, ?_⟩
  rw [ptAt, Equiv.symm_apply_apply]

/-- A nonempty finite set has a positive size. -/
theorem size_pos {S : Set (Space n)} (hS : S.Finite) (hne : S.Nonempty) : 0 < size hS := by
  obtain ⟨x, hx⟩ := hne
  exact Finset.card_pos.2 ⟨x, hS.mem_toFinset.2 hx⟩

/-! ## The parameters -/

/-- The parameter block: accuracy and failure probability both `1`, one cube, one
facet. -/
noncomputable def par (n : ℕ) (hn : 1 ≤ n) : Params where
  ε := 1
  δ := 1
  n := n
  m := max 1 (Nat.card {c : Cube (Fin n ⊕ Fin n) // c ∈ boxDNF n})
  r := max 1 (Nat.card (FacetIndex (boxDNF n)) : ℝ)
  hε0 := one_pos
  hε1 := le_rfl
  hn := hn
  hm := le_max_left _ _
  hr := le_max_left _ _

@[simp] theorem par_eps (hn : 1 ≤ n) : (par n hn).ε = 1 := rfl
@[simp] theorem par_delta (hn : 1 ≤ n) : (par n hn).δ = 1 := rfl
@[simp] theorem par_n (hn : 1 ≤ n) : (par n hn).n = n := rfl

theorem one_le_par_m (hn : 1 ≤ n) : 1 ≤ (par n hn).m := le_max_left _ _

/-- **`cubes_le`**: the parameter block is defined from the cube count. -/
theorem par_cubes_le (hn : 1 ≤ n) :
    (Nat.card {c : Cube (Fin n ⊕ Fin n) // c ∈ boxDNF n} : ℝ) ≤ (par n hn).m := by
  exact_mod_cast Nat.le_max_right 1 _

/-- **`facets_le`**: likewise from the facet count. -/
theorem par_facets_le (hn : 1 ≤ n) :
    (Nat.card (FacetIndex (boxDNF n)) : ℝ) ≤ (par n hn).r := le_max_right _ _

theorem par_epsPrime (hn : 1 ≤ n) : (par n hn).epsPrime = 1 / 12 := by
  rw [Params.epsPrime, par_eps]

theorem par_epsPrime_pos (hn : 1 ≤ n) : 0 < (par n hn).epsPrime := by
  rw [par_epsPrime]; norm_num

/-- The box side: at least `1`, and at least `Thresh`, so that the normalised
count clears the window the epoch estimate needs. -/
noncomputable def side (n : ℕ) (hn : 1 ≤ n) : ℝ := max 1 (par n hn).thresh

theorem one_le_side (hn : 1 ≤ n) : 1 ≤ side n hn := le_max_left _ _

theorem side_pos (hn : 1 ≤ n) : 0 < side n hn := lt_of_lt_of_le one_pos (one_le_side hn)

theorem thresh_le_side (hn : 1 ≤ n) : (par n hn).thresh ≤ side n hn := le_max_right _ _

/-- `γ̂`, the inscribed radius: half the side. -/
noncomputable def gam (n : ℕ) (hn : 1 ≤ n) : ℝ := side n hn / 2

theorem gam_pos (hn : 1 ≤ n) : 0 < gam n hn := by
  rw [gam]; exact half_pos (side_pos hn)

/-- The precision `GetPrecision` returns for this `γ̂`. -/
noncomputable def rho (n : ℕ) (hn : 1 ≤ n) : ℤ := (par n hn).precision (gam n hn)

theorem latticeScale_pos (r : ℤ) : 0 < latticeScale r := by
  rw [latticeScale]; positivity

/-! ## The instance's geometry -/

/-- The atom family. -/
noncomputable def atm (n : ℕ) (hn : 1 ≤ n) : (Fin n ⊕ Fin n) → LinAtom n :=
  boxAtoms n (side n hn)

/-- The box itself. -/
def bx (n : ℕ) (hn : 1 ≤ n) : Set (Space n) :=
  {x : Space n | ∀ k, 0 ≤ x k ∧ x k ≤ side n hn}

theorem sol_eq_bx (hn : 1 ≤ n) :
    sol (fun a => (atm n hn a).halfspace) (boxForm n hn) = bx n hn :=
  sol_boxForm n (side n hn) hn

/-- The box's lattice points at the working precision — finite and nonempty. -/
theorem latFinite (hn : 1 ≤ n) :
    (bx n hn ∩ fineLattice n (latticeScale (rho n hn))).Finite :=
  box_lattice_finite n (side n hn) (latticeScale_pos _)

theorem latNonempty (hn : 1 ≤ n) :
    (bx n hn ∩ fineLattice n (latticeScale (rho n hn))).Nonempty :=
  box_lattice_nonempty n (side_pos hn).le _

/-- How many lattice points the family is indexed by. -/
noncomputable def Lidx (n : ℕ) (hn : 1 ≤ n) : ℕ := size (latFinite hn)

theorem Lidx_pos (hn : 1 ≤ n) : 0 < Lidx n hn := size_pos _ (latNonempty hn)

/-- The enumeration. -/
noncomputable def pt (n : ℕ) (hn : 1 ≤ n) : Fin (Lidx n hn) → Space n := ptAt (latFinite hn)

theorem pt_injective (hn : 1 ≤ n) : Function.Injective (pt n hn) := ptAt_injective _

theorem pt_mem (hn : 1 ≤ n) (i : Fin (Lidx n hn)) :
    pt n hn i ∈ bx n hn ∩ fineLattice n (latticeScale (rho n hn)) := ptAt_mem _ i

/-! ## The count, and that it clears the threshold -/

/-- The normalised lattice count of the instance. -/
noncomputable def Lval (n : ℕ) (hn : 1 ≤ n) : ℝ :=
  normalisedCount (fun a => (atm n hn a).halfspace) (boxForm n hn) (rho n hn)

/-- **The instance is big enough.** `Thresh ≤ c ≤ cⁿ ≤ L`. -/
theorem side_le_Lval (hn : 1 ≤ n) : side n hn ≤ Lval n hn := by
  refine le_trans ?_ (normalisedCount_box_ge n (side_pos hn) hn (rho n hn))
  calc side n hn = side n hn ^ 1 := (pow_one _).symm
    _ ≤ side n hn ^ n := pow_le_pow_right₀ (one_le_side hn) hn

theorem Lval_pos (hn : 1 ≤ n) : 0 < Lval n hn :=
  lt_of_lt_of_le (side_pos hn) (side_le_Lval hn)

/-- `Thresh` is positive for this parameter block: the second branch of the `max`
is `6·log 6`. -/
theorem par_thresh_pos (hn : 1 ≤ n) : 0 < (par n hn).thresh := by
  refine lt_of_lt_of_le ?_ (le_max_right _ _)
  have h6 : (0:ℝ) < Real.log 6 := Real.log_pos (by norm_num)
  have hm : (0:ℝ) ≤ Real.log ((par n hn).m : ℝ) :=
    Real.log_nonneg (by exact_mod_cast one_le_par_m hn)
  rw [par_delta]
  norm_num
  linarith

/-! ## The sampler, and the family's rates

`Ttc.TtcProb` no longer *assumes* the paper's Invariant — `theta_lo`/`theta_hi`
are theorems (`Ttc/Sampler/Bridge.lean`). What the witness has to exhibit instead
is the sampler's own output law (`Ttc.Box.smp`), the fact that it satisfies
`eq:almostuniform` (here *exactly* uniform, the `ε' = 0` centre of the window
rather than a boundary case), and the identity `θ = (sampler mass)·(volume
estimate)` describing how a rate is accumulated.

**That changed the rates, not just their packaging.** The old witness took
`θ s = 1/10^(ρ·n)` — the idealised rate, exactly `L/|Sol(F) ∩ 𝕃ⁿ|`. That value is
*not* `sampD · vol` for any exactly-uniform sampler paired with the exact
`Vol_ED`: it would force `Vol(box)·|box ∩ 𝕃ⁿ| ⁻¹ = 1/10^(ρ·n)`, i.e. `lem:lattice`
holding with equality, which is false. So the rate is now what the algorithm
actually computes, `Vol(box)/|box ∩ 𝕃ⁿ|`, and consequently `∑θ = Vol(box)` rather
than `= L`. The two differ by at most the `(1 ± η)` of `lem:lattice`, which is all
`Ttc.Box.epsPrime_thresh_le_volume` needs.
-/

/-- **The sampler's output law**: exactly uniform on each cube's lattice points.
This is `eq:almostuniform` attained with no error to spend. -/
noncomputable def smp (n : ℕ) (hn : 1 ≤ n) : Cube (Fin n ⊕ Fin n) → Space n → ℝ :=
  fun i _ => 1 / ((region (fun a => (atm n hn a).halfspace) i
    ∩ fineLattice n (latticeScale (rho n hn))).ncard : ℝ)

/-- The box's lattice points are exactly the enumerated ones, so their `Set.ncard`
is `Lidx`. -/
theorem ncard_lat (hn : 1 ≤ n) :
    (bx n hn ∩ fineLattice n (latticeScale (rho n hn))).ncard = Lidx n hn := by
  rw [Lidx, size, Set.ncard_eq_toFinset_card _ (latFinite hn)]

/-! ## Kannan–Vempala on a box

`Ttc.TtcProb` no longer assumes `eq:almostuniform` either: it carries a
`Ttc.KV97Sampler`, the *construction* of `GenerateSamples`, and
`Ttc.TtcProb.samp_unif` derives the contract. So the witness has to build that
construction for the box and check that the law it produces really is
`Ttc.Box.smp`.

It is, and **exactly**: the dilated box `10^ρ·[0,c]ⁿ` is a box, the continuous
draw is taken to be the uniform law on its inflation — so `law_tv` holds at total
variation `0`, hence at every tolerance — and, the one thing that had to be
checked rather than assumed, the rejection-normalised rounding law of that draw is
*literally* the uniform lattice law, with no `(1 ± ε)` slack.

The reason is `Ttc.Box.setIntegral_prodTent_bxInflated`: the tent kernel's
support is the `ℓ∞`-unit box about the lattice point, the inflation displacement
is `κ = √(2 log 48) + √(2 log r) > 1`, and the dilated box's facet normals are
unit vectors, so **every** enumerated point's tent sits entirely inside the
inflated body. Each unnormalised weight is therefore exactly `1`, the sum is
exactly the point count, and the ratio is exactly `1/N`. Had the inflation been
smaller than the rounding radius, boundary points would have carried strictly
less mass than interior ones and the box would *not* have discharged
`sampD_eq` for the uniform `smp`.
-/

/-- The `2n` facet normals of the *dilated* box `10^ρ·[0,c]ⁿ`: the coefficient
vectors of `Ttc.boxAtoms`, read as vectors of `Space n`. They are the unit
vectors `±e_k`, which is what makes the metric inflation `κ‖A j‖` equal to `κ`. -/
noncomputable def bxNormal (n : ℕ) (j : Fin n ⊕ Fin n) : Space n :=
  WithLp.toLp 2 (boxAtoms n 0 j).coeff

@[simp] theorem bxNormal_apply (j : Fin n ⊕ Fin n) (i : Fin n) :
    bxNormal n j i = (boxAtoms n 0 j).coeff i := rfl

/-- The offsets of the dilated box: `x k ≤ 10^ρ·c` and `−x k ≤ 0`. -/
noncomputable def bxOffset (n : ℕ) (hn : 1 ≤ n) : (Fin n ⊕ Fin n) → ℝ
  | .inl _ => latticeScale (rho n hn) * side n hn
  | .inr _ => 0

/-- The inner product against a facet normal is the corresponding coordinate. -/
theorem inner_bxNormal (j : Fin n ⊕ Fin n) (x : Space n) :
    inner ℝ (bxNormal n j) x = ∑ i, (boxAtoms n 0 j).coeff i * x i :=
  Arlib.KV97.inner_eq_sum_coords _ _

/-- **Every facet normal is a unit vector.** -/
theorem norm_bxNormal (j : Fin n ⊕ Fin n) : ‖bxNormal n j‖ = 1 := by
  rw [EuclideanSpace.norm_eq]
  have h : ∀ i : Fin n, ‖bxNormal n j i‖ ^ 2 = ((boxAtoms n 0 j).coeff i) ^ 2 := by
    intro i; rw [bxNormal_apply, Real.norm_eq_abs, sq_abs]
  rw [Finset.sum_congr rfl fun i (_ : i ∈ Finset.univ) => h i]
  cases j with
  | inl k =>
      simp only [boxAtoms_inl_coeff]
      rw [sum_single_sq k (1 : ℝ)]
      simp
  | inr k =>
      simp only [boxAtoms_inr_coeff]
      rw [sum_single_sq k (-1 : ℝ)]
      simp

/-- The dilated box, as a set. -/
noncomputable def dbx (n : ℕ) (hn : 1 ≤ n) : Set (Space n) :=
  {x : Space n | ∀ k, 0 ≤ x k ∧ x k ≤ latticeScale (rho n hn) * side n hn}

/-- **The dilate of the box is the box of side `10^ρ·c`.** -/
theorem smul_bx (hn : 1 ≤ n) : latticeScale (rho n hn) • bx n hn = dbx n hn := by
  have hc : 0 < latticeScale (rho n hn) := latticeScale_pos _
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩ k
    have happ : (latticeScale (rho n hn) • y) k = latticeScale (rho n hn) * y k := rfl
    rw [happ]
    exact ⟨mul_nonneg hc.le (hy k).1, by nlinarith [(hy k).2]⟩
  · intro hx
    refine ⟨(latticeScale (rho n hn))⁻¹ • x, fun k => ?_, ?_⟩
    · have happ : ((latticeScale (rho n hn))⁻¹ • x) k
          = (latticeScale (rho n hn))⁻¹ * x k := rfl
      rw [happ]
      refine ⟨mul_nonneg (by positivity) (hx k).1, ?_⟩
      calc (latticeScale (rho n hn))⁻¹ * x k
          ≤ (latticeScale (rho n hn))⁻¹ * (latticeScale (rho n hn) * side n hn) := by
            have := (hx k).2
            have hinv : (0:ℝ) < (latticeScale (rho n hn))⁻¹ := by positivity
            nlinarith
        _ = side n hn := by field_simp
    · show latticeScale (rho n hn) • (latticeScale (rho n hn))⁻¹ • x = x
      rw [smul_smul, mul_inv_cancel₀ hc.ne', one_smul]

/-- A coordinate atom's linear form evaluates to that coordinate, scaled. -/
theorem sum_single_mul (k : Fin n) (a : ℝ) (x : Space n) :
    ∑ i, (if i = k then a else 0) * x i = a * x k := by
  rw [Finset.sum_eq_single k]
  · simp
  · intro i _ hi; simp [hi]
  · simp

/-- **`dilate_eq` for the box**: the linear system `±x k ≤ (10^ρ·c, 0)` cuts out
the dilated box. -/
theorem bxBody_eq (hn : 1 ≤ n) :
    Arlib.Polytope.body (bxNormal n) (bxOffset n hn) = dbx n hn := by
  ext x
  simp only [Arlib.Polytope.body, Set.mem_setOf_eq, dbx, inner_bxNormal]
  constructor
  · intro h k
    have h1 := h (Sum.inl k)
    have h2 := h (Sum.inr k)
    simp only [boxAtoms_inl_coeff, boxAtoms_inr_coeff, bxOffset, sum_single_mul] at h1 h2
    constructor <;> linarith
  · rintro h (k | k) <;>
      simp only [boxAtoms_inl_coeff, boxAtoms_inr_coeff, bxOffset, sum_single_mul]
    · linarith [(h k).2]
    · linarith [(h k).1]

/-! ### The inflation, and why nothing escapes it -/

/-- The facet-count bound `r` the box is run at. -/
noncomputable def bfac (n : ℕ) : ℝ := max 1 (Fintype.card (Fin n ⊕ Fin n) : ℝ)

theorem one_le_bfac : (1 : ℝ) ≤ bfac n := le_max_left _ _

theorem card_le_bfac : (Fintype.card (Fin n ⊕ Fin n) : ℝ) ≤ bfac n := le_max_right _ _

/-- **`c = √(2 log 48) ≥ 1`.** The tuned Kannan–Vempala constant at the box's
`ε' = 1/12`. This is what makes the inflation wider than the rounding radius in
every coordinate, hence what makes the rejection step lossless here. -/
theorem one_le_cOf_epsPrime (hn : 1 ≤ n) : 1 ≤ Arlib.KV97.cOf (par n hn).epsPrime := by
  have hexp : Real.exp (1 / 2 : ℝ) ≤ 48 := by
    have h1 : Real.exp (1 / 2 : ℝ) ≤ Real.exp 1 := Real.exp_le_exp.2 (by norm_num)
    have h2 : Real.exp 1 < 2.7182818286 := Real.exp_one_lt_d9
    linarith
  have hlog : (1 / 2 : ℝ) ≤ Real.log 48 := (Real.le_log_iff_exp_le (by norm_num)).2 hexp
  rw [Arlib.KV97.cOf, par_epsPrime, show (4 : ℝ) / (1 / 12) = 48 by norm_num,
    Real.one_le_sqrt]
  linarith

/-- **The facet displacement exceeds the rounding radius**, `κ ≥ 1`. -/
theorem one_le_kappa (hn : 1 ≤ n) :
    1 ≤ Arlib.KV97.kappaOf (Arlib.KV97.cOf (par n hn).epsPrime) (bfac n) := by
  have h1 := one_le_cOf_epsPrime hn
  have h2 : (0:ℝ) ≤ Real.sqrt (2 * Real.log (bfac n)) := Real.sqrt_nonneg _
  rw [Arlib.KV97.kappaOf]
  linarith

/-- The inflated dilated box `P'`, the body the continuous sampler draws from. -/
noncomputable def bxInflated (n : ℕ) (hn : 1 ≤ n) : Set (Space n) :=
  Arlib.KV97.inflated (bxNormal n) (bxOffset n hn)
    (Arlib.KV97.cOf (par n hn).epsPrime) (bfac n)

/-- **The rounding kernel of a point of the dilated box is supported inside the
inflation.** The tent about `z` reaches at most `1` in each coordinate, the
normals are unit vectors, and `κ ≥ 1`. -/
theorem roundBox_subset_bxInflated (hn : 1 ≤ n) {z : Space n} (hz : z ∈ dbx n hn) :
    Arlib.Lattice.Rounding.roundBox z ⊆ bxInflated n hn := by
  intro p hp
  have hk := one_le_kappa hn
  refine Arlib.KV97.mem_inflated.2 fun j => ?_
  rw [inner_bxNormal, norm_bxNormal, mul_one]
  cases j with
  | inl k =>
      have habs := abs_le.1 (hp k : |p k - z k| ≤ 1)
      have hzk := (hz k).2
      simp only [boxAtoms_inl_coeff, bxOffset, sum_single_mul]
      linarith [habs.2]
  | inr k =>
      have habs := abs_le.1 (hp k : |p k - z k| ≤ 1)
      have hzk := (hz k).1
      simp only [boxAtoms_inr_coeff, bxOffset, sum_single_mul]
      linarith [habs.1]

/-- **The rejection step is lossless on the box.** The rounding kernel of any
point of the dilated box puts *all* of its mass inside `P'`, so the unnormalised
weight `Pr[rnd p = z]` of the uniform continuous density is exactly `1` — not
merely inside Kannan–Vempala's `(1 ± ε)` window.

This is the fact the witness turns on, and it is the reason the box's `sampD` can
be the *exactly* uniform lattice law. -/
theorem setIntegral_prodTent_bxInflated (hn : 1 ≤ n) {z : Space n} (hz : z ∈ dbx n hn) :
    ∫ p in bxInflated n hn, Arlib.Lattice.Rounding.prodTent z p = 1 := by
  have hmeas : MeasurableSet (bxInflated n hn) :=
    Arlib.KV97.measurableSet_inflated _ _ _ _
  have hzero : Set.EqOn (Arlib.Lattice.Rounding.prodTent z) (fun _ => (0:ℝ))
      (bxInflated n hn)ᶜ := fun p hp =>
    Arlib.Lattice.Rounding.prodTent_eq_zero_of_notMem
      fun hbox => hp (roundBox_subset_bxInflated hn hz hbox)
  have h0 : ∫ p in (bxInflated n hn)ᶜ, Arlib.Lattice.Rounding.prodTent z p = 0 := by
    rw [MeasureTheory.setIntegral_congr_fun hmeas.compl hzero]
    simp
  rw [Arlib.Lattice.Rounding.setIntegral_prodTent_compl z hmeas, h0, sub_zero]

/-! ### `P'` has positive finite volume, and the draw is *exactly* uniform on it

`Ttc.KV97Sampler` now carries a **law** and a total-variation bound rather than a
density, and the tolerance is `ε'/(4·Vol(P'))`. So the witness owes three things
it did not owe before: that `Vol(P')` is neither `0` nor `∞` (else the uniform
reference law is not a probability measure), and that `contVol` really is
`Vol(P')`. All three come from the same place — the dilated box `dbx` contains an
`ℓ₂`-ball and has finite volume, and `P' ⊇ dbx`. -/

/-- The dilated box's side, `10^ρ·c`, is positive. -/
theorem dbx_side_pos (hn : 1 ≤ n) : 0 < latticeScale (rho n hn) * side n hn :=
  mul_pos (latticeScale_pos _) (side_pos hn)

/-- The dilated box contains an `ℓ₂`-ball of radius `10^ρ·c/2`. -/
theorem ball_subset_dbx (hn : 1 ≤ n) :
    Metric.ball (boxCentre n (latticeScale (rho n hn) * side n hn))
        ((latticeScale (rho n hn) * side n hn) / 2)
      ⊆ Arlib.Polytope.body (bxNormal n) (bxOffset n hn) := by
  rw [bxBody_eq hn]
  exact ball_subset_box n _

/-- **`Vol(P') ≠ 0`.** `P'` contains the dilated box, which contains a ball. -/
theorem volume_bxInflated_ne_zero (hn : 1 ≤ n) :
    MeasureTheory.volume (bxInflated n hn) ≠ 0 :=
  Arlib.KV97.volume_inflated_ne_zero (half_pos (dbx_side_pos hn)) Arlib.KV97.cOf_nonneg
    (ball_subset_dbx hn)

/-- **`Vol(P') ≠ ∞`.** The dilated box is bounded, and inflating a body with an
inscribed ball multiplies its volume by at most `(1 + κ/γ)ⁿ`. -/
theorem volume_bxInflated_ne_top (hn : 1 ≤ n) :
    MeasureTheory.volume (bxInflated n hn) ≠ ⊤ :=
  Arlib.KV97.volume_inflated_ne_top (half_pos (dbx_side_pos hn)) Arlib.KV97.cOf_nonneg
    (ball_subset_dbx hn) (by rw [bxBody_eq hn]; exact volume_box_ne_top n _)

theorem volume_bxInflated_toReal_pos (hn : 1 ≤ n) :
    0 < (MeasureTheory.volume (bxInflated n hn)).toReal :=
  ENNReal.toReal_pos (volume_bxInflated_ne_zero hn) (volume_bxInflated_ne_top hn)

/-- **The continuous draw is the uniform law on `P'` itself**, so its
total-variation distance to uniform is `0` and `law_tv` holds at every tolerance —
the `ε' = 0` centre of the hypothesis, not a boundary case of it.

This is route 2 of `Arlib/MarkovChains/Continuous/PointwiseRoute.lean`: the
witness gets exact uniformity because its `P'` *is* the proposal region, so the
rejection step is free. That is a witness, not an algorithm — see that file's
`uniformOn_ball_ball` for why the trick does not generalise. -/
theorem bxLaw_isProb (hn : 1 ≤ n) :
    MeasureTheory.IsProbabilityMeasure
      (Arlib.uniformOn MeasureTheory.volume (bxInflated n hn)) :=
  Arlib.isProbabilityMeasure_uniformOn _ (volume_bxInflated_ne_zero hn)
    (volume_bxInflated_ne_top hn)

/-- **Every enumerated point's unnormalised weight is exactly `1/Vol(P')`.**

`Ttc.Box.setIntegral_prodTent_bxInflated` says the whole rounding kernel of a
point of the dilated box sits inside `P'`, so the uniform average of the kernel is
`Vol(P')⁻¹ · 1`. This is what makes the box's `sampD` the *exactly* uniform
lattice law. -/
theorem integral_prodTent_bxUniform (hn : 1 ≤ n) {z : Space n} (hz : z ∈ dbx n hn) :
    ∫ p, Arlib.Lattice.Rounding.prodTent z p
        ∂(Arlib.uniformOn MeasureTheory.volume (bxInflated n hn))
      = (MeasureTheory.volume (bxInflated n hn)).toReal⁻¹ := by
  rw [Arlib.integral_uniformOn_real, setIntegral_prodTent_bxInflated hn hz, mul_one]

/-- The single cube of the box's DNF, so every per-cube field can be discharged
uniformly. -/
theorem region_of_mem (hn : 1 ≤ n)
    (i : {c : Cube (Fin n ⊕ Fin n) // c ∈ Ttc.toDNF (boxForm n hn)}) :
    region (fun a => (atm n hn a).halfspace) i.val = bx n hn := by
  have hi : i.val = boxCube n := by
    have : i.val ∈ boxDNF n := by rw [← toDNF_boxForm hn]; exact i.property
    simpa [boxDNF] using this
  rw [hi]
  simp only [atm]
  exact region_boxCube n (side n hn)

/-- **The dilated cube has finitely many integer points** — the image of the
box's fine-lattice points under the dilation. -/
theorem dilFinite (hn : 1 ≤ n)
    (i : {c : Cube (Fin n ⊕ Fin n) // c ∈ Ttc.toDNF (boxForm n hn)}) :
    ((latticeScale (rho n hn) • region (fun a => (atm n hn a).halfspace) i.val)
        ∩ intLattice n : Set (Space n)).Finite := by
  rw [region_of_mem hn i]
  have h : (latticeScale (rho n hn) • bx n hn ∩ intLattice n : Set (Space n))
      = (fun x => latticeScale (rho n hn) • x) ''
          (bx n hn ∩ fineLattice n (latticeScale (rho n hn))) :=
    (Arlib.Lattice.image_smul_inter_fineLattice (latticeScale_pos _) (bx n hn)).symm
  rw [h]
  exact (latFinite hn).image _

/-- Each point's level-`0` rate: the sampler's mass at it, times the cube's volume
estimate — `Ttc.TtcProb.theta_eq` on the nose. -/
noncomputable def th (n : ℕ) (hn : 1 ≤ n) : Fin (Lidx n hn) → ℝ :=
  fun _ => 1 / ((bx n hn ∩ fineLattice n (latticeScale (rho n hn))).ncard : ℝ)
    * (volume (bx n hn)).toReal

/-- **`Lidx` is the box's lattice-point count.** -/
theorem Lidx_eq_count (hn : 1 ≤ n) :
    (Lidx n hn : ℝ)
      = (latticeCount (fun a => (atm n hn a).halfspace) (boxForm n hn) (rho n hn) : ℝ) := by
  have h : latticeCount (fun a => (atm n hn a).halfspace) (boxForm n hn) (rho n hn)
      = (latFinite hn).toFinset.card := by
    rw [latticeCount, sol_eq_bx hn, Set.ncard_eq_toFinset_card _ (latFinite hn)]
  rw [h, Lidx, size]

/-- **The rates sum to the volume estimate.** Every point carries `Vol(box)/N` and
there are `N` of them, so the total is `Vol(box)` exactly. -/
theorem sum_th (hn : 1 ≤ n) : ∑ s, th n hn s = (volume (bx n hn)).toReal := by
  have hL : (Lidx n hn : ℝ) ≠ 0 := Nat.cast_ne_zero.2 (Lidx_pos hn).ne'
  simp only [th, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  rw [ncard_lat hn]
  field_simp

theorem totalRate_th (hn : 1 ≤ n) (j : ℕ) :
    totalRate (th n hn) j = (volume (bx n hn)).toReal / 2 ^ j := by
  rw [totalRate, sum_th]

/-! ## The epoch index -/

/-- **The instance clears the bottom of the epoch window.** -/
theorem epsPrime_thresh_le_Lval (hn : 1 ≤ n) :
    (1 - (par n hn).epsPrime) * (par n hn).thresh / 8 ≤ Lval n hn := by
  have hT := par_thresh_pos hn
  have hep : (par n hn).epsPrime = 1 / 12 := par_epsPrime hn
  have hs := side_le_Lval hn
  have hts := thresh_le_side hn
  rw [hep]
  have h1 : (1 - 1 / 12 : ℝ) * (par n hn).thresh / 8 ≤ (par n hn).thresh := by linarith
  linarith

/-- **`lem:lattice` for the witness, lower half.** `Ttc.lattice_of_dnf` at the
box's own DNF — every hypothesis it wants is one `Ttc.Box.boxProb` discharges
anyway, but it is needed here, *before* the instance exists, to bound the total
rate `∑θ = Vol(box)` from below. Nothing new is assumed. -/
theorem lattice_lo_bx (hn : 1 ≤ n) :
    (1 - (par n hn).eta) * Lval n hn ≤ (volume (bx n hn)).toReal := by
  have hb : ∀ i : {c : Cube (Fin n ⊕ Fin n) // c ∈ boxDNF n}, i.val = boxCube n :=
    fun i => by simpa [boxDNF] using i.property
  have h := lattice_of_dnf (atm n hn) (boxDNF_isDNFOf hn) boxDNF_isPositive
    (par n hn) rfl (par_cubes_le hn) (par_facets_le hn)
    (boxAtoms_normal_ne_zero n (side n hn))
    (fun _ => boxCentre n (side n hn)) (gam_pos hn)
    (fun i => by rw [hb i]; exact ball_subset_region_boxCube n (side n hn))
    (fun i => by rw [hb i]; exact volume_region_boxCube_ne_top n (side n hn))
    (rfl : rho n hn = (par n hn).precision (gam n hn))
  have hlo := h.1.1
  rwa [volSol, sol_eq_bx hn] at hlo

/-- **The instance clears the bottom of the epoch window**, for the total rate
`∑θ = Vol(box)`. `lem:lattice` costs a factor `1 − η = 7/8`; the window's bottom
is `(1 − ε')/8 = 11/96` of `Thresh`, so there is an order of magnitude to
spare. -/
theorem epsPrime_thresh_le_volume (hn : 1 ≤ n) :
    (1 - (par n hn).epsPrime) * (par n hn).thresh / 8 ≤ (volume (bx n hn)).toReal := by
  have hlat := lattice_lo_bx hn
  have hη : (par n hn).eta = 1 / 8 := by rw [Params.eta, par_eps]
  have hep : (par n hn).epsPrime = 1 / 12 := par_epsPrime hn
  have hs := side_le_Lval hn
  have hts := thresh_le_side hn
  have hT := par_thresh_pos hn
  rw [hη] at hlat
  rw [hep]
  linarith

/-- **A usable epoch index exists for this instance.** -/
theorem exists_jstar (hn : 1 ≤ n) :
    ∃ jstar : ℕ, 1 ≤ jstar ∧
      2 * totalRate (th n hn) (jstar - 1) ≤ (par n hn).thresh ∧
      (1 - (par n hn).epsPrime) * (par n hn).thresh / 8 ≤ totalRate (th n hn) (jstar - 1) := by
  obtain ⟨jstar, hj1, h2, h3⟩ := exists_epoch (S := (volume (bx n hn)).toReal)
    (Thresh := (par n hn).thresh) (epsP := (par n hn).epsPrime) (par_thresh_pos hn)
    (par_epsPrime_pos hn).le (epsPrime_thresh_le_volume hn)
  exact ⟨jstar, hj1, by rwa [totalRate_th], by rwa [totalRate_th]⟩

/-! ## The oracles

`vol` is the exact volume estimate `L` (this is the ideal instance — `Vol_ED`
returns the truth), every point is covered by the single cube, and the randomness
is the coupled family read directly.
-/

/-- The only cube. -/
theorem eq_boxCube {c : Cube (Fin n ⊕ Fin n)} (h : c ∈ boxDNF n) : c = boxCube n := by
  simpa [boxDNF] using h

/-- The volume estimate: the exact volume — the ideal `Vol_ED`, with error `0`. -/
noncomputable def vl (n : ℕ) (hn : 1 ≤ n) : Cube (Fin n ⊕ Fin n) → ℝ :=
  fun _ => (volume (bx n hn)).toReal

/-- The box has positive, finite volume: it contains a ball of radius `c/2`. -/
theorem volume_bx_pos (hn : 1 ≤ n) : 0 < (volume (bx n hn)).toReal := by
  have hbpos : 0 < volume (Metric.ball (boxCentre n (side n hn)) (side n hn / 2)) :=
    Metric.measure_ball_pos _ _ (by have := side_pos hn; positivity)
  have hle : volume (Metric.ball (boxCentre n (side n hn)) (side n hn / 2))
      ≤ volume (bx n hn) := measure_mono (ball_subset_box n (side n hn))
  exact ENNReal.toReal_pos (by exact ne_of_gt (lt_of_lt_of_le hbpos hle))
    (volume_box_ne_top n (side n hn))

/-- The coverage test: the single cube covers everything. -/
def cov (n : ℕ) : Space n → Cube (Fin n ⊕ Fin n) → Bool := fun _ _ => true

/-- Cube membership on the enumerated points. -/
def mm (n : ℕ) (hn : 1 ≤ n) : Cube (Fin n ⊕ Fin n) → Fin (Lidx n hn) → Bool := fun _ _ => true

/-- The oracle bundle: the coupled family, read directly. -/
noncomputable def orc (n : ℕ) (hn : 1 ≤ n) :
    (ℕ → (Fin (Lidx n hn) → ℕ)) → Oracles n (Cube (Fin n ⊕ Fin n)) :=
  fun t => trajOracles (pt_injective hn) (vl n hn) (cov n) (mm n hn) t

theorem cov_eq (hn : 1 ≤ n) (s : Fin (Lidx n hn)) (i : Cube (Fin n ⊕ Fin n)) :
    cov n (pt n hn s) i = mm n hn i s := rfl

theorem cover_all (hn : 1 ≤ n) (s : Fin (Lidx n hn)) :
    ((boxDNF n).any fun i => mm n hn i s) = true := by
  simp [boxDNF, mm]

theorem exists_mm (hn : 1 ≤ n) (i : Cube (Fin n ⊕ Fin n)) : ∃ s, mm n hn i s = true :=
  ⟨⟨0, Lidx_pos hn⟩, rfl⟩

/-! ## The instance -/

/-- **A non-degenerate `Ttc.TtcProb`.** The box `[0,c]ⁿ` with `c ≥ Thresh`, sampled
by the coupled family. The solution set is nonempty, `L` is positive and at least
`Thresh`, and the `lem:numlattice` obligation is discharged by
`Ttc.numlattice_union_of_traj` — a proof, not a vacuity. -/
noncomputable def boxProb (n : ℕ) (hn : 1 ≤ n) : TtcProb (Fin n ⊕ Fin n) n where
  ε := 1
  δ := 1
  hε0 := one_pos
  hε1 := le_rfl
  hδ0 := one_pos
  hδ1 := le_rfl
  atoms := atm n hn
  M := fun a => (atm n hn a).halfspace
  M_eq := rfl
  φ := boxForm n hn
  toDNF := Ttc.toDNF
  isDNF := toDNF_isDNFOf _
  isPositive := toDNF_isPositive (boxForm_isPositive hn)
  Ω := ℕ → (Fin (Lidx n hn) → ℕ)
  mΩ := inferInstance
  μ := trajLaw (th n hn)
  isProb := inferInstance
  P := par n hn
  eps_eq := rfl
  delta_eq := rfl
  dim_eq := rfl
  cubes_le := by rw [toDNF_boxForm hn]; exact par_cubes_le hn
  facets_le := by rw [toDNF_boxForm hn]; exact par_facets_le hn
  normal_ne_zero := by rw [toDNF_boxForm hn]; exact boxAtoms_normal_ne_zero n (side n hn)
  O := orc n hn
  cen := fun _ => boxCentre n (side n hn)
  gammaHat := gam n hn
  hgammaHat := gam_pos hn
  ball_subset := by
    rw [toDNF_boxForm hn]
    intro i
    rw [eq_boxCube i.property]
    exact ball_subset_region_boxCube n (side n hn)
  volume_ne_top := by
    rw [toDNF_boxForm hn]
    intro i
    rw [eq_boxCube i.property]
    exact volume_region_boxCube_ne_top n (side n hn)
  ρ := rho n hn
  rho_eq := rfl
  gen_mem := by
    rw [toDNF_boxForm hn]
    intro t i j N hi x hx
    rw [eq_boxCube hi] at hx ⊢
    simp only [atm]
    rw [region_boxCube n (side n hn)]
    simp only [orc] at hx
    exact gen_mem_trajOracles (T := fun _ => bx n hn ∩ fineLattice n (latticeScale (rho n hn)))
      (pt_injective hn) t (fun _ s _ => pt_mem hn s) (exists_mm hn _) j N (rho n hn) x hx
  L := Lval n hn
  L_eq := rfl
  Lidx := Lidx n hn
  ptE := pt n hn
  ptE_inj := pt_injective hn
  ptE_mem := by
    intro s
    rw [sol_eq_bx hn]
    exact pt_mem hn s
  ptE_onto := by
    intro x hx
    rw [sol_eq_bx hn] at hx
    exact exists_ptAt _ hx
  θ := th n hn
  vol := vl n hn
  -- `GenerateSamples` is Kannan–Vempala's sampler run on the dilated box, and
  -- because the inflation `κ ≥ 1` swallows the whole rounding kernel of every
  -- enumerated point (`Ttc.Box.setIntegral_prodTent_bxInflated`), the law it
  -- returns is the *exactly* uniform one. `eq:almostuniform` is no longer a
  -- field — `Ttc.TtcProb.samp_unif` derives it — so nothing quantitative is
  -- asserted here, and neither is the paper's Invariant.
  sampD := smp n hn
  sampler :=
    { J := Fin n ⊕ Fin n
      Amat := fun _ => bxNormal n
      bvec := fun _ => bxOffset n hn
      -- the field asks only for `⊆`; the box in fact satisfies the equality
      -- `Ttc.Box.bxBody_eq`, of which this is the `⊇` half
      dilate_eq := fun i => by rw [region_of_mem hn i, smul_bx hn]; exact (bxBody_eq hn).ge
      facetBound := bfac n
      one_le_facetBound := one_le_bfac
      card_le_facetBound := card_le_bfac
      contLaw := fun _ => Arlib.uniformOn volume (bxInflated n hn)
      isProbContLaw := fun _ => bxLaw_isProb hn
      contVol := fun _ => (volume (bxInflated n hn)).toReal
      contVol_pos := fun _ => volume_bxInflated_toReal_pos hn
      -- `bxInflated` is *defined* as the inflation of `bxNormal`/`bxOffset`, so
      -- the field that pins `contVol` to `Vol(P')` is `rfl` here
      contVol_eq := fun _ => rfl
      -- the draw is the uniform law on `P'` itself, so the total-variation
      -- distance is `0` and the field holds at every tolerance
      law_tv := fun _ => (Arlib.TVLe.refl _).mono (by simp)
      sampD_eq := by
        intro i x hx
        -- the rejection sum is a `finsum`, so the sampler assumes no `Fintype`;
        -- the box supplies one from `Ttc.Box.dilFinite` and converts
        letI : Fintype ((latticeScale (rho n hn)
            • region (fun a => (atm n hn a).halfspace) i.val)
              ∩ intLattice n : Set (Space n)) := (dilFinite hn i).fintype
        have hVne : (volume (bxInflated n hn)).toReal⁻¹ ≠ 0 :=
          inv_ne_zero (volume_bxInflated_toReal_pos hn).ne'
        have hdb : ∀ z ∈ latticeScale (rho n hn)
            • region (fun a => (atm n hn a).halfspace) i.val,
            (∫ p, Arlib.Lattice.Rounding.prodTent z p
                ∂(Arlib.uniformOn volume (bxInflated n hn)))
              = (volume (bxInflated n hn)).toReal⁻¹ := by
          intro z hz
          have hz' : z ∈ dbx n hn := by
            rw [← smul_bx hn, ← region_of_mem hn i]; exact hz
          exact integral_prodTent_bxUniform hn hz'
        have hxmem : latticeScale (rho n hn) • x
            ∈ latticeScale (rho n hn) • region (fun a => (atm n hn a).halfspace) i.val :=
          ⟨x, hx.1, rfl⟩
        have hsum : ∀ k : ((latticeScale (rho n hn)
            • region (fun a => (atm n hn a).halfspace) i.val)
              ∩ intLattice n : Set (Space n)),
            (∫ p, Arlib.Lattice.Rounding.prodTent (k : Space n) p
                ∂(Arlib.uniformOn volume (bxInflated n hn)))
              = (volume (bxInflated n hn)).toReal⁻¹ :=
          fun k => hdb k.1 k.2.1
        rw [finsum_eq_sum_of_fintype, hdb _ hxmem,
          Finset.sum_congr rfl (fun k _ => hsum k)]
        simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
          ← Nat.card_eq_fintype_card, Nat.card_coe_set_eq]
        rw [← Ttc.ncard_inter_fineLattice (latticeScale_pos _), mul_comm, ← div_div,
          div_self hVne]
        rfl }
  theta_eq := by
    intro s
    have hreg : region (fun a => (atm n hn a).halfspace) (boxCube n) = bx n hn := by
      simp only [atm]; exact region_boxCube n (side n hn)
    refine ⟨boxCube n, by rw [toDNF_boxForm hn]; exact List.mem_singleton_self _,
      by rw [hreg]; exact (pt_mem hn s).1, ?_⟩
    simp only [th, smp, vl, hreg]
  cover := cov n
  memPt := mm n hn
  memPt_eq := by
    rw [toDNF_boxForm hn]
    intro i hi s
    rw [eq_boxCube hi]
    simp only [atm]
    rw [region_boxCube n (side n hn)]
    exact ⟨fun _ => (pt_mem hn s).1, fun _ => rfl⟩
  toTraj := fun t => t
  toTraj_meas := aemeasurable_id
  law_eq := Measure.map_id
  oracle_eq := fun _ => rfl
  cover_eq := cov_eq hn
  -- `Vol_ED` is the exact oracle: it returns `Vol(K)` on the nose and never
  -- fails, so it is a `Ttc.VolumeAlgorithm` (`Ttc.VolumeAlgorithm.exact`) whose
  -- coin space is `Unit`. The witness stays as non-degenerate as before — the
  -- estimates are the true volumes, which is the `ε' = 0`, `δ' = 0` corner of
  -- Theorem 1.1, not an appeal to emptiness.
  volAlg := VolumeAlgorithm.exact n
  volCoins := ()
  volED_eq := by
    intro i hi
    have hi' : i ∈ boxDNF n := by rwa [toDNF_boxForm hn] at hi
    have hreg : region (fun a => (atm n hn a).halfspace) i = bx n hn := by
      rw [eq_boxCube hi']; exact region_boxCube n (side n hn)
    show (volume (bx n hn)).toReal
        = gam n hn ^ n * (volume (roundBody (boxCentre n (side n hn)) (gam n hn)
            (region (fun a => (atm n hn a).halfspace) i))).toReal
    rw [hreg]
    exact toReal_volume_eq (gam_pos hn)
  volCoins_good := by
    rw [toDNF_boxForm hn]
    intro i hi
    have hreg : region (fun a => (atm n hn a).halfspace) i = bx n hn := by
      rw [eq_boxCube hi]; exact region_boxCube n (side n hn)
    rw [hreg]
    have h0 : (0:ℝ) ≤ (volume (bx n hn)).toReal := ENNReal.toReal_nonneg
    have he := par_epsPrime_pos hn
    show (volume (bx n hn)).toReal ∈ Set.Icc _ _
    constructor <;> [skip; skip] <;> nlinarith
  vol_pos := fun _ _ => volume_bx_pos hn
  big := by rw [sum_th hn]; exact epsPrime_thresh_le_volume hn

/-- **`Ttc.TtcProb` is inhabited, non-degenerately**, so
`Ttc.TtcProb.volume_estimate` is not vacuous — and, unlike the old degenerate
witness, not vacuous for a reason that would also make the theorem uninformative. -/
theorem nonempty_ttcProb (n : ℕ) (hn : 1 ≤ n) : Nonempty (TtcProb (Fin n ⊕ Fin n) n) :=
  ⟨boxProb n hn⟩

/-- **The `Vol_ED` failure budget is not an empty hypothesis.**
`Ttc.TtcProb.volGood_prob_budget` needs the loop count against the parameter
block's `m`; the box supplies it, so the `1 − δ/4` bound is instantiable and the
witness exercises it. -/
theorem boxProb_numCubes_le (hn : 1 ≤ n) :
    (((boxProb n hn).numCubes : ℕ) : ℝ) ≤ ((boxProb n hn).P.m : ℝ) := by
  have hlen : (boxProb n hn).numCubes = 1 := by
    show (Ttc.toDNF (boxForm n hn)).length = 1
    rw [toDNF_boxForm hn]
    rfl
  rw [hlen]
  exact_mod_cast one_le_par_m hn

/-- **The `m` `Vol_ED` calls of the witness succeed with probability at least
`1 − δ/4`** — the union bound, applied to a real instance. -/
theorem boxProb_volGood (hn : 1 ≤ n) :
    1 - (boxProb n hn).δ / 4
      ≤ ((boxProb n hn).volAlg.μ (boxProb n hn).volEvent).toReal :=
  (boxProb n hn).volGood_prob_budget (boxProb_numCubes_le hn)

end Box

end Ttc

/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import Ttc.Analysis.Witness
import Ttc.Analysis.NumLatticeModel

/-!
# A non-degenerate witness

The development's original witness (`trivialProb`) inhabited `Ttc.TtcProb`
degenerately: empty DNF, `Sol(F) = ∅`, `L = 0`, so the failure event was empty and
every estimate held vacuously. CLAUDE.md §11 asks for better, and
`Ttc.numlattice_union_of_traj` makes better possible — a witness whose failure
bound is *proved*, not sidestepped. `trivialProb` has since been removed outright:
once `Ttc.TtcProb` carries the sampler fields, `D = []` forces `Lidx = 0` and
contradicts `θ_pos`, so no degenerate instance exists at all.

The instance is the box `[0,c]ⁿ` of `Analysis/Witness`, sampled by the coupled
family of `Analysis/Coupling`. The one real constraint is that the estimate is
only meaningful when the count clears the threshold, so the side `c` is chosen
from `Thresh` — which `Ttc.normalisedCount_box_ge` permits, since its bound
`cⁿ ≤ L` holds at every precision `ρ` and so does not depend on `ρ` being fixed
first.
-/

namespace Ttc

namespace Box

open MeasureTheory

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

theorem par_epsPrime_le_one (hn : 1 ≤ n) : (par n hn).epsPrime ≤ 1 := by
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

/-! ## The family's rates

Spread `L` evenly over the lattice points. The total is then `L` *exactly*, so
`Ttc.window_of_exact` discharges the accuracy window with no error to spend —
the ideal instance of CLAUDE.md §13.
-/

/-- Each point's level-`0` rate. -/
noncomputable def th (n : ℕ) (hn : 1 ≤ n) : Fin (Lidx n hn) → ℝ :=
  fun _ => Lval n hn / (Lidx n hn : ℝ)

theorem th_nonneg (hn : 1 ≤ n) (s : Fin (Lidx n hn)) : 0 ≤ th n hn s :=
  div_nonneg (Lval_pos hn).le (Nat.cast_nonneg _)

/-- **The rates reproduce the count exactly.** -/
theorem sum_th (hn : 1 ≤ n) : ∑ s, th n hn s = Lval n hn := by
  have hne : ((Lidx n hn : ℝ)) ≠ 0 := Nat.cast_ne_zero.2 (Lidx_pos hn).ne'
  simp only [th, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  field_simp

theorem sum_th_pos (hn : 1 ≤ n) : 0 < ∑ s, th n hn s := by
  rw [sum_th]; exact Lval_pos hn

theorem totalRate_th (hn : 1 ≤ n) (j : ℕ) :
    totalRate (th n hn) j = Lval n hn / 2 ^ j := by
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

/-- **A usable epoch index exists for this instance.** -/
theorem exists_jstar (hn : 1 ≤ n) :
    ∃ jstar : ℕ, 1 ≤ jstar ∧
      2 * totalRate (th n hn) (jstar - 1) ≤ (par n hn).thresh ∧
      (1 - (par n hn).epsPrime) * (par n hn).thresh / 8 ≤ totalRate (th n hn) (jstar - 1) := by
  obtain ⟨jstar, hj1, h2, h3⟩ := exists_epoch (S := Lval n hn) (Thresh := (par n hn).thresh)
    (epsP := (par n hn).epsPrime) (Lval_pos hn) (par_thresh_pos hn)
    (par_epsPrime_pos hn).le (epsPrime_thresh_le_Lval hn)
  exact ⟨jstar, hj1, by rwa [totalRate_th], by rwa [totalRate_th]⟩

/-! ## The oracles

`vol` is the exact volume estimate `L` (this is the ideal instance — `Vol_ED`
returns the truth), every point is covered by the single cube, and the randomness
is the coupled family read directly.
-/

/-- The only cube. -/
theorem eq_boxCube {c : Cube (Fin n ⊕ Fin n)} (h : c ∈ boxDNF n) : c = boxCube n := by
  simpa [boxDNF] using h

/-- The volume estimate: exact. -/
noncomputable def vl (n : ℕ) (hn : 1 ≤ n) : Cube (Fin n ⊕ Fin n) → ℝ := fun _ => Lval n hn

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

/-- The epoch index this instance runs to. -/
noncomputable def js (n : ℕ) (hn : 1 ≤ n) : ℕ := (exists_jstar hn).choose

theorem js_ge (hn : 1 ≤ n) : 1 ≤ js n hn := (exists_jstar hn).choose_spec.1

theorem js_rate_le (hn : 1 ≤ n) :
    2 * totalRate (th n hn) (js n hn - 1) ≤ (par n hn).thresh :=
  (exists_jstar hn).choose_spec.2.1

theorem js_lamStar_ge (hn : 1 ≤ n) :
    (1 - (par n hn).epsPrime) * (par n hn).thresh / 8 ≤ totalRate (th n hn) (js n hn - 1) :=
  (exists_jstar hn).choose_spec.2.2

theorem js_rate_small (hn : 1 ≤ n) (i : Cube (Fin n ⊕ Fin n)) :
    ¬ ((par n hn).thresh / vl n hn i ≤ (1 / 2 : ℝ) ^ (js n hn - 1)) :=
  rate_small_of_epoch (Lval_pos hn) (by
    have := js_rate_le hn
    rwa [totalRate_th] at this)

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
  D := boxDNF n
  isDNF := boxDNF_isDNFOf hn
  isPositive := boxDNF_isPositive
  Ω := ℕ → (Fin (Lidx n hn) → ℕ)
  mΩ := inferInstance
  μ := trajLaw (th n hn)
  isProb := inferInstance
  P := par n hn
  eps_eq := rfl
  delta_eq := rfl
  dim_eq := rfl
  cubes_le := par_cubes_le hn
  facets_le := par_facets_le hn
  normal_ne_zero := boxAtoms_normal_ne_zero n (side n hn)
  O := orc n hn
  fuel := 0
  cen := fun _ => boxCentre n (side n hn)
  gammaHat := gam n hn
  hgammaHat := gam_pos hn
  ball_subset := by
    intro i
    rw [eq_boxCube i.property]
    exact ball_subset_region_boxCube n (side n hn)
  volume_ne_top := by
    intro i
    rw [eq_boxCube i.property]
    exact volume_region_boxCube_ne_top n (side n hn)
  ρ := rho n hn
  rho_eq := rfl
  gen_mem := by
    intro t c i j N hi x hx
    rw [eq_boxCube hi] at hx ⊢
    simp only [atm]
    rw [region_boxCube n (side n hn)]
    simp only [orc] at hx
    exact gen_mem_trajOracles (T := fun _ => bx n hn ∩ fineLattice n (latticeScale (rho n hn)))
      (pt_injective hn) t (fun _ s _ => pt_mem hn s) (exists_mm hn _) c j N (rho n hn) x hx
  L := Lval n hn
  L_eq := rfl
  Lidx := Lidx n hn
  ptE := pt n hn
  ptE_inj := pt_injective hn
  θ := th n hn
  θ_nonneg := th_nonneg hn
  θ_pos := sum_th_pos hn
  vol := vl n hn
  cover := cov n
  memPt := mm n hn
  toTraj := fun t => t
  toTraj_meas := aemeasurable_id
  law_eq := Measure.map_id
  oracle_eq := fun _ => rfl
  cover_eq := cov_eq hn
  cover_all := cover_all hn
  jstar := js n hn
  hjstar := js_ge hn
  rate_small := fun i _ => js_rate_small hn i
  rate_le := js_rate_le hn
  lamStar_ge := js_lamStar_ge hn
  rate_eq_L := sum_th hn

/-- **`Ttc.TtcProb` is inhabited, non-degenerately**, so
`Ttc.TtcProb.volume_estimate` is not vacuous — and, unlike the old degenerate
witness, not vacuous for a reason that would also make the theorem uninformative. -/
theorem nonempty_ttcProb (n : ℕ) (hn : 1 ≤ n) : Nonempty (TtcProb (Fin n ⊕ Fin n) n) :=
  ⟨boxProb n hn⟩

end Box

end Ttc

/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import Ttc.Exec.Inputs

/-!
# `Exec/Scale`: dilating the input formula

`Ttc.ttc_volume_vol` carries `hvol : P.thresh / 4 ≤ volSol (atomSet atoms) φ`, and
that hypothesis is **not** an artefact of the analysis.  TTC's estimator is a
Poisson sketch whose mean `Λ` is bounded above by `Vol(Sol F)`; a Poisson count of
mean `Λ` has relative standard deviation `Λ^(-1/2)`, so it cannot concentrate to
relative accuracy `ε` unless `Λ ≳ Thresh`.  A body of tiny volume is simply
invisible to the sketch.  No sharper analysis of the *same* run removes the
hypothesis.

What removes it is **changing the run**.  Volume is homogeneous of degree `n`:
`Vol(c·S) = cⁿ·Vol(S)` exactly, for every measurable `S` and every `c > 0`.  So
the algorithm can dilate its input by an explicit factor `c ≥ 1`, run TTC on the
dilated formula — whose solution set now has volume `cⁿ·Vol(Sol F)`, as large as
we like — and divide the returned estimate by `cⁿ`.  Relative error is invariant
under that rescaling, so a `(1±ε)` guarantee for the dilate is a `(1±ε)` guarantee
for the original.

**This is a change to what the algorithm does, not a strengthening of the
analysis.**  It is a preprocessing step the paper does not have (README finding
20): `alg:ttc` as written runs on `F` itself, and on a small `F` it provably fails
the regime condition.  The honest statement is that we verify a *modified*
algorithm — TTC preceded by a dilation and followed by a division — and that the
modification is free because the dilation is an exact volume identity rather than
an approximation.

## What is in this file

The **dilation algebra**: everything about what scaling does to the input data.
`Ttc.scaleAtoms` itself is a *definition of the amended algorithm*, so it lives in
`Model/Pseudocode` (line A11) and only its theory is here.
`Ttc.scaleAtoms c atoms` keeps every normal vector and multiplies every bound by
`c`, which dilates each half-space by `c` (`Ttc.halfspace_scaleAtoms`).  From that
one fact everything else is structural:

| Lemma | Says |
| --- | --- |
| `Ttc.halfspace_scaleAtoms` | `(scaleAtoms c atoms a).halfspace = c • (atoms a).halfspace` |
| `Ttc.sol_scaleAtoms` | `Sol` of the dilate is the dilate of `Sol` |
| `Ttc.region_scaleAtoms` | same for a cube's region |
| `Ttc.volSol_scaleAtoms` | `Vol` of the dilate is `cⁿ·Vol` |
| `Ttc.isBounded_sol_scaleAtoms` | boundedness transports |
| `Ttc.coeff_scaleAtoms` | normals are untouched, so `hcoeff` transports |
| `Ttc.ball_subset_scaleAtoms` | an inscribed ball of radius `γ̂` becomes one of radius `c·γ̂` |

The scale factor `c` itself — how large it has to be, and the proof that it makes
`hvol` true — is not here.

Note that `Ttc.sol_scaleAtoms` and `Ttc.region_scaleAtoms` need **no positivity
hypothesis on the formula**: they hold for every `Ttc.BForm`, negations included,
because dilation by an invertible scalar is a bijection of the space and therefore
commutes with every Boolean operation on membership.
-/

namespace Ttc

open MeasureTheory Set Pointwise

variable {A : Type*} {n : ℕ}

/-! ## The dilation

`Ttc.scaleAtoms` — line A11 of the preprocessing — is **defined in
`Model/Pseudocode`**, with the rest of the amended algorithm's vocabulary. Only
the theorems about it are here. -/

/-- The normals are untouched.  This is what transports `hcoeff` (no atom is
degenerate) from the original formula to the dilate. -/
theorem coeff_scaleAtoms (c : ℝ) (atoms : A → LinAtom n) (a : A) :
    (scaleAtoms c atoms a).coeff = (atoms a).coeff := rfl

@[simp]
theorem bound_scaleAtoms (c : ℝ) (atoms : A → LinAtom n) (a : A) :
    (scaleAtoms c atoms a).bound = c * (atoms a).bound := rfl

/-! ## The crux: dilating an atom dilates its half-space -/

/-- The linear form of an atom is unchanged by dilating the point back: `⟪a, c⁻¹·x⟫
= c⁻¹·⟪a, x⟫`.  Pulled out as a lemma because it is the only place the
`EuclideanSpace` coordinate representation of a scalar multiple is touched. -/
theorem sum_coeff_inv_smul (c : ℝ) (a : LinAtom n) (x : Space n) :
    ∑ i, a.coeff i * (c⁻¹ • x) i = c⁻¹ * ∑ i, a.coeff i * x i := by
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp [PiLp.smul_apply, smul_eq_mul]
  ring

/-- **The crux.**  Multiplying an atom's bound by `c > 0` dilates the half-space it
denotes by `c`. -/
theorem halfspace_scaleAtoms {c : ℝ} (hc : 0 < c) (atoms : A → LinAtom n) (a : A) :
    (scaleAtoms c atoms a).halfspace = c • (atoms a).halfspace := by
  have hc0 : c ≠ 0 := ne_of_gt hc
  ext x
  rw [Set.mem_smul_set_iff_inv_smul_mem₀ hc0]
  show (∑ i, (atoms a).coeff i * x i ≤ c * (atoms a).bound)
    ↔ (∑ i, (atoms a).coeff i * (c⁻¹ • x) i ≤ (atoms a).bound)
  rw [sum_coeff_inv_smul, inv_mul_le_iff₀ hc]

/-! ## Everything else, structurally

Dilation by `c ≠ 0` is a bijection of `Ttc.Space n`, so membership in the dilate at
`x` is membership in the original at `c⁻¹ • x`, atom by atom.  Boolean structure
then rides along for free. -/

/-- The Boolean assignment induced by the dilated atoms at `x` is the one induced
by the original atoms at `c⁻¹ • x`. -/
theorem induced_scaleAtoms {c : ℝ} (hc : 0 < c) (atoms : A → LinAtom n) (x : Space n) :
    induced (atomSet (scaleAtoms c atoms)) x
      = induced (atomSet atoms) (c⁻¹ • x) := by
  funext a
  have h : (scaleAtoms c atoms a).halfspace = c • (atoms a).halfspace :=
    halfspace_scaleAtoms hc atoms a
  show (x ∈ (scaleAtoms c atoms a).halfspace) = (c⁻¹ • x ∈ (atoms a).halfspace)
  rw [h, Set.mem_smul_set_iff_inv_smul_mem₀ (ne_of_gt hc)]

/-- **`Sol` commutes with dilation.**  Holds for *every* `Ttc.BForm`, negations
included: no positivity hypothesis is needed, because `x ↦ c⁻¹ • x` is a bijection
and `Ttc.BForm.holds` is built from membership by Boolean connectives alone. -/
theorem sol_scaleAtoms {c : ℝ} (hc : 0 < c) (atoms : A → LinAtom n) (φ : BForm A) :
    sol (atomSet (scaleAtoms c atoms)) φ = c • sol (atomSet atoms) φ := by
  ext x
  rw [Set.mem_smul_set_iff_inv_smul_mem₀ (ne_of_gt hc)]
  show φ.holds (induced (atomSet (scaleAtoms c atoms)) x)
    ↔ φ.holds (induced (atomSet atoms) (c⁻¹ • x))
  rw [induced_scaleAtoms hc]

/-- **A cube's region commutes with dilation.**  Same proof as
`Ttc.sol_scaleAtoms`, and again with no hypothesis on the cube's literals. -/
theorem region_scaleAtoms {c : ℝ} (hc : 0 < c) (atoms : A → LinAtom n) (cube : Cube A) :
    region (atomSet (scaleAtoms c atoms)) cube = c • region (atomSet atoms) cube := by
  ext x
  rw [Set.mem_smul_set_iff_inv_smul_mem₀ (ne_of_gt hc)]
  show cube.holds (induced (atomSet (scaleAtoms c atoms)) x)
    ↔ cube.holds (induced (atomSet atoms) (c⁻¹ • x))
  rw [induced_scaleAtoms hc]

/-! ## The volume identity, which is the whole point -/

/-- **`Vol(Sol(c·F)) = cⁿ · Vol(Sol F)`.**  Lebesgue measure on `ℝⁿ` is homogeneous
of degree `n` (`Ttc.volume_smul_body`), so dilating the input multiplies the
quantity the algorithm estimates by exactly `cⁿ`.

No finiteness hypothesis: if the volume is infinite then `ENNReal.toReal` sends
both sides to `0`. -/
theorem volSol_scaleAtoms {c : ℝ} (hc : 0 < c) (atoms : A → LinAtom n) (φ : BForm A) :
    volSol (atomSet (scaleAtoms c atoms)) φ = c ^ n * volSol (atomSet atoms) φ := by
  show (volume (sol (atomSet (scaleAtoms c atoms)) φ)).toReal
    = c ^ n * (volume (sol (atomSet atoms) φ)).toReal
  rw [sol_scaleAtoms hc, volume_smul_body hc.le, ENNReal.toReal_mul,
    ENNReal.toReal_ofReal (pow_nonneg hc.le n)]

/-! ## Transporting the remaining hypotheses -/

/-- **Boundedness transports.**  `hbdd` is necessary (an unbounded `Sol` has
infinite volume, which `Ttc.volSol` reports as `0`), and dilation preserves it. -/
theorem isBounded_sol_scaleAtoms {c : ℝ} (hc : 0 < c) {atoms : A → LinAtom n} {φ : BForm A}
    (h : Bornology.IsBounded (sol (atomSet atoms) φ)) :
    Bornology.IsBounded (sol (atomSet (scaleAtoms c atoms)) φ) := by
  rw [sol_scaleAtoms hc]
  exact h.smul₀ c

/-- **The inscribed ball transports, with its radius scaled.**  A ball of radius
`γ̂` inside `region i` becomes a ball of radius `c·γ̂` inside the dilated region —
so the dilated instance still has the inscribed-ball data `alg:ttc` needs, at
centre `c • cen i`. -/
theorem ball_subset_scaleAtoms {c gammaHat : ℝ} (hc : 0 < c) {atoms : A → LinAtom n}
    {D : DNF A} {cen : {d : Cube A // d ∈ D} → Space n}
    (h : ∀ i, Metric.ball (cen i) gammaHat ⊆ region (atomSet atoms) i.val) :
    ∀ i, Metric.ball (c • cen i) (c * gammaHat)
      ⊆ region (atomSet (scaleAtoms c atoms)) i.val := by
  intro i
  rw [region_scaleAtoms hc]
  exact ball_radius_scales hc _ _ (h i)

end Ttc

/-! ## Axiom profile -/

#print axioms Ttc.coeff_scaleAtoms
#print axioms Ttc.bound_scaleAtoms
#print axioms Ttc.sum_coeff_inv_smul
#print axioms Ttc.halfspace_scaleAtoms
#print axioms Ttc.induced_scaleAtoms
#print axioms Ttc.sol_scaleAtoms
#print axioms Ttc.region_scaleAtoms
#print axioms Ttc.volSol_scaleAtoms
#print axioms Ttc.isBounded_sol_scaleAtoms
#print axioms Ttc.ball_subset_scaleAtoms

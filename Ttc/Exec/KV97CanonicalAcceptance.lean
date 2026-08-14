import Ttc.Exec.KV97TVAcceptance
import Ttc.Exec.KV97CanonicalThin
import Ttc.Exec.CanonPolytope
import Ttc.Sampler.Bridge

/-!
# KV97 `1/8` acceptance on TTC's canonical cubes

This specializes the measure-valued TV acceptance theorem to the exact canonical
half-space description of a TTC cube.  All geometry, lattice-count, escape, and
thin-inflation premises are discharged from `TtcProb`; the only remaining input
is the continuous sampler's TV guarantee.
-/

namespace Ttc.KV97CanonicalAcceptance

open MeasureTheory ProbabilityTheory Set Pointwise
open Ttc.KV97RoundedEndpointBridge
open scoped ENNReal Classical BigOperators

abbrev State (n : Nat) := EuclideanSpace Real (Fin n)

variable {A : Type*} {n : Nat}

/-- The operational randomized-rounding acceptance probability on every actual
TTC canonical cube is at least `1/8`.  The continuous law may have atoms; only
the same TV guarantee used by the hybrid sampler is required. -/
theorem one_eighth_le_roundedMeasure_canonical_of_tvLe
    (T : TtcProb A n) (i : {c : Cube A // c ∈ T.toDNF T.φ})
    (mu : Measure (State n)) [IsProbabilityMeasure mu]
    (htv : Arlib.TVLe mu
      (Arlib.uniformOn volume
        (Arlib.KV97.inflated
          (canonAm T.atoms (T.toDNF T.φ) i)
          (canonBv T.atoms (T.toDNF T.φ) (latticeScale T.ρ) i)
          (Arlib.KV97.cOf T.P.epsPrime) T.P.r))
      (ENNReal.ofReal (T.P.epsPrime / (4 *
        (volume (Arlib.KV97.inflated
          (canonAm T.atoms (T.toDNF T.φ) i)
          (canonBv T.atoms (T.toDNF T.φ) (latticeScale T.ρ) i)
          (Arlib.KV97.cOf T.P.epsPrime) T.P.r)).toReal)))) :
    ENNReal.ofReal ((1 : Real) / 8) ≤
      Ttc.CostedKV97Rounding.roundedMeasure mu
        (integerAcceptance T.M T.ρ i.val) := by
  let J := Fin (Nat.card (FacetIndex (T.toDNF T.φ)))
  let Am : J → State n := canonAm T.atoms (T.toDNF T.φ) i
  let bv : J → Real := canonBv T.atoms (T.toDNF T.φ) (latticeScale T.ρ) i
  let K0 := Arlib.Polytope.body Am bv
  let K := Arlib.KV97.inflated Am bv (Arlib.KV97.cOf T.P.epsPrime) T.P.r
  let Z := {z : Fin n → Int // z ∈ integerAcceptance T.M T.ρ i.val}
  have hbody : K0 = latticeScale T.ρ • region T.M i.val := by
    dsimp only [K0, Am, bv]
    rw [canon_body_eq_smul_region T.atoms T.isPositive (latticeScale_pos T.ρ) i]
    rw [T.M_eq]
  have hgamma : 0 < latticeScale T.ρ * T.gammaHat :=
    mul_pos (latticeScale_pos _) T.hgammaHat
  have hball : Metric.ball (latticeScale T.ρ • T.cen i)
      (latticeScale T.ρ * T.gammaHat) ⊆ K0 := by
    rw [hbody]
    exact ball_radius_scales (latticeScale_pos T.ρ) _ _ (T.ball_subset i)
  have hfin : volume K0 ≠ ⊤ := by
    rw [hbody, volume_smul_body (latticeScale_pos T.ρ).le]
    exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top (T.volume_ne_top i)
  have hK0 : volume K ≠ 0 :=
    Arlib.KV97.volume_inflated_ne_zero hgamma Arlib.KV97.cOf_nonneg hball
  have hKtop : volume K ≠ ⊤ :=
    Arlib.KV97.volume_inflated_ne_top hgamma Arlib.KV97.cOf_nonneg hball hfin
  let Lset := ((latticeScale T.ρ • region T.M i.val) ∩ intLattice n : Set (State n))
  letI : Fintype Lset := (T.dilate_intLattice_finite i).fintype
  let e := acceptedEquiv T.M T.ρ i.val
  letI : Fintype Z := Fintype.ofEquiv Lset e.symm
  have hcardFine : (Fintype.card Z : Real) =
      ((region T.M i.val ∩ fineLattice n (latticeScale T.ρ)).ncard : Real) := by
    have hc : Fintype.card Z = Fintype.card Lset := Fintype.card_congr e
    rw [hc]
    rw [← Nat.card_eq_fintype_card, Nat.card_coe_set_eq]
    rw [show Lset.ncard =
        (region T.M i.val ∩ fineLattice n (latticeScale T.ρ)).ncard by
      exact (ncard_inter_fineLattice (latticeScale_pos T.ρ) _).symm]
  have hlattice : (volume K0).toReal ≤ (1 + T.P.eta) * (Fintype.card Z : Real) := by
    have hcube := T.lattice_cube_hi i.property
    rw [hbody, volume_smul_body (latticeScale_pos T.ρ).le,
      ENNReal.toReal_mul,
      ENNReal.toReal_ofReal (pow_nonneg (latticeScale_pos T.ρ).le n), hcardFine]
    have hs : 0 < latticeScale T.ρ ^ n := pow_pos (latticeScale_pos _) _
    calc
      latticeScale T.ρ ^ n * (volume (region T.M i.val)).toReal
          ≤ latticeScale T.ρ ^ n *
              ((1 + T.P.eta) *
                (((region T.M i.val ∩ fineLattice n (latticeScale T.ρ)).ncard : Real) /
                  latticeScale T.ρ ^ n)) := mul_le_mul_of_nonneg_left hcube hs.le
      _ = (1 + T.P.eta) *
          ((region T.M i.val ∩ fineLattice n (latticeScale T.ρ)).ncard : Real) := by
            field_simp
  have hthin : Arlib.KV97.kappaOf (Arlib.KV97.cOf T.P.epsPrime) T.P.r /
      (latticeScale T.ρ * T.gammaHat) ≤ 1 / (n : Real) := by
    have h := kv97_kappaOf_epsPrime_div_scaledRadius_le T.P T.hgammaHat
    simpa [T.rho_eq, T.dim_eq] using h
  have heta0 : 0 ≤ T.P.eta := by
    unfold Params.eta
    linarith [T.P.hε0]
  have heta4 : T.P.eta ≤ 1 / 4 := by
    unfold Params.eta
    linarith [T.P.hε1]
  have htheta0 : 0 ≤ T.P.epsPrime / 4 := by
    exact div_nonneg T.P.epsPrime_pos.le (by norm_num)
  have hloss : T.P.epsPrime / 4 + T.P.epsPrime / 4 ≤ 1 / 4 := by
    unfold Params.epsPrime
    linarith [T.P.hε1]
  have htv' : Arlib.TVLe mu (Arlib.uniformOn volume K)
      (ENNReal.ofReal ((T.P.epsPrime / 4) / (volume K).toReal)) := by
    simpa [K, Am, bv, div_div] using htv
  have henum : ∀ z,
      Arlib.KV97.latEmb n z ∈ latticeScale T.ρ • region T.M i.val ↔
        ∃ j : Z, j.1 = z := by
    intro z
    simp only [integerAcceptance, mem_preimage]
    constructor
    · intro hz
      exact ⟨⟨z, hz⟩, rfl⟩
    · rintro ⟨j, rfl⟩
      exact j.2
  have hesc : ∀ j : Z, ∫ p in Kᶜ,
      Arlib.Lattice.Rounding.prodTent (Arlib.KV97.latEmb n j.1) p ≤
        T.P.epsPrime / 4 := by
    intro j
    have hjbody : Arlib.KV97.latEmb n j.1 ∈ K0 := by
      rw [hbody]
      exact j.2
    have hcardJ : (Fintype.card J : Real) ≤ T.P.r := by
      simpa [J] using T.facets_le
    have h := escape_of_mem_body (eps := T.P.epsPrime)
      Am bv T.P.hr hcardJ hjbody
    have hexp := Arlib.KV97.exp_cOf T.P.epsPrime_pos (by
      unfold Params.epsPrime
      linarith [T.P.hε1])
    simpa [K, hexp] using h
  exact Ttc.KV97TVAcceptance.one_eighth_le_roundedMeasure_integerAcceptance_of_tvLe
    mu T.M T.ρ i.val Am bv (latticeScale T.ρ • T.cen i)
    (latticeScale T.ρ * T.gammaHat) (Arlib.KV97.cOf T.P.epsPrime) T.P.r
    (T.P.epsPrime / 4) (T.P.epsPrime / 4) T.P.eta (fun j : Z => j.1)
    hgamma Arlib.KV97.cOf_nonneg hball hfin heta0 heta4 htheta0 hloss
    htv' hK0 hKtop hlattice hthin Subtype.val_injective henum hesc

#print axioms one_eighth_le_roundedMeasure_canonical_of_tvLe

end Ttc.KV97CanonicalAcceptance

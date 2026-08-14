import Ttc.Exec.PolyHybridAccuracy
import Ttc.Exec.SampleDischarge
import Ttc.Sampler.ConstructHybridUncond

/-!
# A concrete hybrid sampler certificate at TTC's canonical data

The start is uniform on the known inscribed ball.  For the constructor's
closed-ball hypothesis we use half its radius; the low-dimensional walk step
is chosen to be that same half-radius.  All polytope geometry and warmness are
then discharged by `SampleDischarge`.
-/

namespace Ttc.ConcreteHybridCanonicalOwnerPoly

open MeasureTheory ProbabilityTheory Set Pointwise
open Ttc.KV97RoundedEndpointBridge
open scoped ENNReal BigOperators Classical

variable {A : Type*} {n : Nat}
variable (atoms : A → LinAtom n) (phi : BForm A) (eps delta : Real)

noncomputable def canonicalHybridCenter (i : CubeIndex atoms phi) : Space n :=
  latticeScale (ttcPrec atoms phi eps delta) • ttcCen atoms phi eps delta i

noncomputable def canonicalHybridInnerRadius (_ : CubeIndex atoms phi) : Real :=
  ttcSampInradius atoms phi eps delta / 2

noncomputable def canonicalHybridOuterRadius (i : CubeIndex atoms phi) : Real :=
  ttcSampDiam atoms phi eps delta i

noncomputable def canonicalHybridStep (_ : CubeIndex atoms phi) : Real :=
  ttcSampInradius atoms phi eps delta / 2

noncomputable def canonicalHybridWarm (i : CubeIndex atoms phi) : Real :=
  ttcSampWarm atoms phi eps delta i

noncomputable def canonicalHybridStart (i : CubeIndex atoms phi) : Measure (Space n) :=
  Arlib.uniformOn volume
    (Metric.ball (canonicalHybridCenter atoms phi eps delta i)
      (ttcSampInradius atoms phi eps delta))

set_option maxHeartbeats 1000000 in
/-- The unconditional hybrid `KV97Sampler`, constructed entirely from TTC's
canonical geometry and its explicit uniform-ball warm start. -/
noncomputable def kv97Sampler_polyHybridCanonical
    (h_eps_pos : 0 < eps) (h_eps_le : eps ≤ 1) (hn : 1 ≤ n)
    (hphi : phi.IsPositive) (hvol : 0 < volSol (atomSet atoms) phi) :
    KV97Sampler A n (M atoms phi eps delta) (D atoms phi)
      (rho atoms phi eps delta) (algBlock atoms phi eps delta).epsPrime
      (polyHybridSampD atoms phi eps delta
        (canonicalHybridInnerRadius atoms phi eps delta)
        (canonicalHybridOuterRadius atoms phi eps delta)
        (canonicalHybridStep atoms phi eps delta)
        (canonicalHybridWarm atoms phi eps delta)
        (canonicalHybridStart atoms phi eps delta)) := by
  have hepsPrime : 0 < (algBlock atoms phi eps delta).epsPrime :=
    (algBlock atoms phi eps delta).epsPrime_pos
  have hPr : (algBlock atoms phi eps delta).r =
      (Nat.card (FacetIndex (D atoms phi)) : Real) :=
    ttcBlock_r atoms phi eps delta h_eps_pos h_eps_le hn hphi hvol
  have hrf : (algBlock atoms phi eps delta).r = canonRfac (D atoms phi) := by
    rw [hPr, canonRfac]
  apply kv97SamplerOfHybridUncond hn hepsPrime
    (Fin (Nat.card (FacetIndex (D atoms phi))))
    (canonAm (algAtoms atoms phi eps delta) (D atoms phi))
    (canonBv (algAtoms atoms phi eps delta) (D atoms phi)
      (latticeScale (rho atoms phi eps delta)))
    (zin := canonicalHybridCenter atoms phi eps delta)
    (rin := canonicalHybridInnerRadius atoms phi eps delta)
    (zout := canonicalHybridCenter atoms phi eps delta)
    (Rout := canonicalHybridOuterRadius atoms phi eps delta)
    (δ := canonicalHybridStep atoms phi eps delta)
    (sigma := canonicalHybridStart atoms phi eps delta)
    (Mw := canonicalHybridWarm atoms phi eps delta)
  · intro i
    exact canon_smul_region_subset_body (algAtoms atoms phi eps delta)
      (toDNFd_isPositive (preprocess_isPositive atoms phi))
      (latticeScale_pos (rho atoms phi eps delta)) i
  · exact (algBlock atoms phi eps delta).hr
  · rw [Fintype.card_fin, hPr]
  · intro i
    unfold canonicalHybridInnerRadius
    have hr := ttcSampInradius_pos atoms phi eps delta
      h_eps_pos h_eps_le hn hphi hvol
    linarith
  · intro i
    rw [hrf]
    change Metric.closedBall (canonicalHybridCenter atoms phi eps delta i)
        (canonicalHybridInnerRadius atoms phi eps delta i) ⊆
      ttcSampBody atoms phi eps delta i
    unfold canonicalHybridCenter canonicalHybridInnerRadius
    exact (Metric.closedBall_subset_ball (by
      have hr := ttcSampInradius_pos atoms phi eps delta
        h_eps_pos h_eps_le hn hphi hvol
      linarith)).trans
        (ball_subset_ttcSampBody atoms phi eps delta
          h_eps_pos h_eps_le hn hphi hvol i)
  · intro i
    unfold canonicalHybridOuterRadius
    exact ttcSampDiam_pos atoms phi eps delta h_eps_pos h_eps_le hn hphi hvol i
  · intro i y hy
    rw [hrf] at hy
    change y ∈ Metric.closedBall (canonicalHybridCenter atoms phi eps delta i)
      (canonicalHybridOuterRadius atoms phi eps delta i)
    unfold canonicalHybridCenter canonicalHybridOuterRadius
    rw [Metric.mem_closedBall, dist_comm]
    apply dist_le_ttcSampDiam atoms phi eps delta h_eps_pos h_eps_le hn hphi hvol i
    · exact (ball_subset_ttcSampBody atoms phi eps delta
        h_eps_pos h_eps_le hn hphi hvol i)
        (Metric.mem_ball_self
          (ttcSampInradius_pos atoms phi eps delta
            h_eps_pos h_eps_le hn hphi hvol))
    · exact hy
  · intro i
    unfold canonicalHybridStep
    have hr := ttcSampInradius_pos atoms phi eps delta
      h_eps_pos h_eps_le hn hphi hvol
    linarith
  · intro i
    rfl
  · intro i
    rw [hrf]
    change ttcSampTol atoms phi eps delta i ≤ 1
    exact ttcSampTol_le_one atoms phi eps delta h_eps_pos h_eps_le hn hphi hvol i
  · intro i
    unfold canonicalHybridStart
    exact Arlib.isProbabilityMeasure_uniformOn_ball volume _
      (ttcSampInradius_pos atoms phi eps delta h_eps_pos h_eps_le hn hphi hvol)
  · intro i
    exact one_le_ttcSampWarm atoms phi eps delta h_eps_pos h_eps_le hn hphi hvol i
  · intro i
    rw [hrf]
    change Arlib.IsWarm
      (ENNReal.ofReal (ttcSampWarm atoms phi eps delta i))
      (Arlib.uniformOn volume
        (Metric.ball
          (latticeScale (ttcPrec atoms phi eps delta) • ttcCen atoms phi eps delta i)
          (ttcSampInradius atoms phi eps delta)))
      (Arlib.uniformOn volume (ttcSampBody atoms phi eps delta i))
    exact isWarm_ttcSampWarm atoms phi eps delta h_eps_pos h_eps_le hn hphi hvol i

theorem tvLe_polyHybridCanonical
    (h_eps_pos : 0 < eps) (h_eps_le : eps ≤ 1) (hn : 1 ≤ n)
    (hphi : phi.IsPositive) (hvol : 0 < volSol (atomSet atoms) phi)
    (i : CubeIndex atoms phi) :
    Arlib.TVLe
      (polyHybridContLaw atoms phi eps delta
        (canonicalHybridInnerRadius atoms phi eps delta)
        (canonicalHybridOuterRadius atoms phi eps delta)
        (canonicalHybridStep atoms phi eps delta)
        (canonicalHybridWarm atoms phi eps delta)
        (canonicalHybridStart atoms phi eps delta) i)
      (Arlib.uniformOn volume
        (Arlib.KV97.inflated
          (canonAm (algAtoms atoms phi eps delta) (D atoms phi) i)
          (canonBv (algAtoms atoms phi eps delta) (D atoms phi)
            (latticeScale (rho atoms phi eps delta)) i)
          (Arlib.KV97.cOf (algBlock atoms phi eps delta).epsPrime)
          (algBlock atoms phi eps delta).r))
      (ENNReal.ofReal ((algBlock atoms phi eps delta).epsPrime / (4 *
        (volume (Arlib.KV97.inflated
          (canonAm (algAtoms atoms phi eps delta) (D atoms phi) i)
          (canonBv (algAtoms atoms phi eps delta) (D atoms phi)
            (latticeScale (rho atoms phi eps delta)) i)
          (Arlib.KV97.cOf (algBlock atoms phi eps delta).epsPrime)
          (algBlock atoms phi eps delta).r)).toReal))) := by
  exact (kv97Sampler_polyHybridCanonical atoms phi eps delta
    h_eps_pos h_eps_le hn hphi hvol).law_tv i

set_option maxHeartbeats 1000000 in
/-- The KV97 rejection probability bound for the concrete canonical hybrid
draw.  This is the algorithm-data counterpart of
`one_eighth_le_roundedMeasure_canonical_of_tvLe`. -/
theorem one_eighth_le_roundedMeasure_polyHybridCanonical
    (h_eps_pos : 0 < eps) (h_eps_le : eps ≤ 1) (hn : 1 ≤ n)
    (hphi : phi.IsPositive) (hvol : 0 < volSol (atomSet atoms) phi)
    (i : CubeIndex atoms phi) :
    ENNReal.ofReal ((1 : Real) / 8) ≤
      Ttc.CostedKV97Rounding.roundedMeasure
        (polyHybridContLaw atoms phi eps delta
          (canonicalHybridInnerRadius atoms phi eps delta)
          (canonicalHybridOuterRadius atoms phi eps delta)
          (canonicalHybridStep atoms phi eps delta)
          (canonicalHybridWarm atoms phi eps delta)
          (canonicalHybridStart atoms phi eps delta) i)
        (integerAcceptance (M atoms phi eps delta)
          (rho atoms phi eps delta) i.val) := by
  let P := algBlock atoms phi eps delta
  let M0 := M atoms phi eps delta
  let D0 := D atoms phi
  let rho0 := rho atoms phi eps delta
  let J := Fin (Nat.card (FacetIndex D0))
  let Am : J → Space n := canonAm (algAtoms atoms phi eps delta) D0 i
  let bv : J → Real := canonBv (algAtoms atoms phi eps delta) D0
    (latticeScale rho0) i
  let K0 := Arlib.Polytope.body Am bv
  let K := Arlib.KV97.inflated Am bv (Arlib.KV97.cOf P.epsPrime) P.r
  let mu := polyHybridContLaw atoms phi eps delta
    (canonicalHybridInnerRadius atoms phi eps delta)
    (canonicalHybridOuterRadius atoms phi eps delta)
    (canonicalHybridStep atoms phi eps delta)
    (canonicalHybridWarm atoms phi eps delta)
    (canonicalHybridStart atoms phi eps delta) i
  let Z := {z : Fin n → Int // z ∈ integerAcceptance M0 rho0 i.val}
  have hPr : P.r = (Nat.card (FacetIndex D0) : Real) :=
    ttcBlock_r atoms phi eps delta h_eps_pos h_eps_le hn hphi hvol
  have hbody : K0 = latticeScale rho0 • region M0 i.val := by
    dsimp only [K0, Am, bv, M0, D0, rho0]
    exact canon_body_eq_smul_region (algAtoms atoms phi eps delta)
      (toDNFd_isPositive (preprocess_isPositive atoms phi))
      (latticeScale_pos (algPrec atoms phi eps delta)) i
  have hgamma : 0 < latticeScale rho0 * algGamma atoms phi eps delta :=
    mul_pos (latticeScale_pos _) (algGamma_pos_of_isPositive atoms phi eps delta hphi hvol)
  have hball : Metric.ball
      (latticeScale rho0 • algCen atoms phi eps delta i)
      (latticeScale rho0 * algGamma atoms phi eps delta) ⊆ K0 := by
    rw [hbody]
    exact ball_radius_scales (latticeScale_pos rho0) _ _
      (ball_subset_algCen atoms phi eps delta i)
  have hbdd : Bornology.IsBounded
      (sol M0 (preprocess atoms phi)) :=
    algAtoms_bdd atoms phi eps delta h_eps_pos h_eps_le hn hphi hvol
  have hfinRegion : ∀ j : CubeIndex atoms phi,
      volume (region M0 j.val) ≠ ⊤ :=
    volume_region_ne_top_of_isBounded (toDNFd_isDNFOf _) hbdd
  have hfin : volume K0 ≠ ⊤ := by
    rw [hbody, volume_smul_body (latticeScale_pos rho0).le]
    exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top (hfinRegion i)
  have hK0 : volume K ≠ 0 :=
    Arlib.KV97.volume_inflated_ne_zero hgamma Arlib.KV97.cOf_nonneg hball
  have hKtop : volume K ≠ ⊤ :=
    Arlib.KV97.volume_inflated_ne_top hgamma Arlib.KV97.cOf_nonneg hball hfin
  have hnP : P.n = n :=
    ttcBlock_n atoms phi eps delta h_eps_pos h_eps_le hn hphi hvol
  have hm1 : (1 : Real) ≤ P.m := by exact_mod_cast P.hm
  have hfac : (Nat.card (FacetIndex D0) : Real) ≤ P.r := by rw [hPr]
  have hAnz : ∀ j : FacetIndex D0,
      0 < ∑ k, ((algAtoms atoms phi eps delta) j.2.val.atom).coeff k ^ 2 :=
    normal_ne_zero_of_coeff_ne_zero (preprocess_coeff atoms phi hphi hvol)
  have hfiniteFine :
      (region M0 i.val ∩ fineLattice n (latticeScale rho0)).Finite :=
    finite_region_lattice_of_dnf (algAtoms atoms phi eps delta)
      (toDNFd_isPositive (preprocess_isPositive atoms phi)) P hnP hm1 hfac hAnz
      (algCen atoms phi eps delta)
      (algGamma_pos_of_isPositive atoms phi eps delta hphi hvol)
      (ball_subset_algCen atoms phi eps delta) hfinRegion rfl i
  let Lset := ((latticeScale rho0 • region M0 i.val) ∩ intLattice n : Set (Space n))
  letI : Fintype Lset := by
    have hdil : Lset.Finite := by
      rw [show Lset = (latticeScale rho0 • region M0 i.val) ∩ intLattice n by rfl,
        ← smul_inter_fineLattice (latticeScale_ne_zero rho0)]
      exact hfiniteFine.image _
    exact hdil.fintype
  let e := Ttc.KV97RoundedEndpointBridge.acceptedEquiv M0 rho0 i.val
  letI : Fintype Z := Fintype.ofEquiv Lset e.symm
  have hcardFine : (Fintype.card Z : Real) =
      ((region M0 i.val ∩ fineLattice n (latticeScale rho0)).ncard : Real) := by
    have hc : Fintype.card Z = Fintype.card Lset := Fintype.card_congr e
    rw [hc, ← Nat.card_eq_fintype_card, Nat.card_coe_set_eq]
    exact_mod_cast (ncard_inter_fineLattice (latticeScale_pos rho0)
      (region M0 i.val)).symm
  have hcube := lattice_cube_hi_of_dnf (algAtoms atoms phi eps delta)
    (toDNFd_isPositive (preprocess_isPositive atoms phi)) P hnP hm1 hfac hAnz
    (algCen atoms phi eps delta)
    (algGamma_pos_of_isPositive atoms phi eps delta hphi hvol)
    (ball_subset_algCen atoms phi eps delta) hfinRegion rfl i
  have hlattice : (volume K0).toReal ≤ (1 + P.eta) * (Fintype.card Z : Real) := by
    rw [hbody, volume_smul_body (latticeScale_pos rho0).le,
      ENNReal.toReal_mul,
      ENNReal.toReal_ofReal (pow_nonneg (latticeScale_pos rho0).le n), hcardFine]
    have hs : 0 < latticeScale rho0 ^ n := pow_pos (latticeScale_pos _) _
    calc
      latticeScale rho0 ^ n * (volume (region M0 i.val)).toReal
          ≤ latticeScale rho0 ^ n * ((1 + P.eta) *
              (((region M0 i.val ∩ fineLattice n (latticeScale rho0)).ncard : Real) /
                latticeScale rho0 ^ n)) := mul_le_mul_of_nonneg_left hcube hs.le
      _ = (1 + P.eta) *
          ((region M0 i.val ∩ fineLattice n (latticeScale rho0)).ncard : Real) := by
            field_simp
  have hthin : Arlib.KV97.kappaOf (Arlib.KV97.cOf P.epsPrime) P.r /
      (latticeScale rho0 * algGamma atoms phi eps delta) ≤ 1 / (n : Real) := by
    have h := kv97_kappaOf_epsPrime_div_scaledRadius_le P
      (algGamma_pos_of_isPositive atoms phi eps delta hphi hvol)
    have hrho : rho0 = P.precision (algGamma atoms phi eps delta) := rfl
    rw [hrho]
    simpa [hnP] using h
  have heta0 : 0 ≤ P.eta := by
    unfold Params.eta
    linarith [P.hε0]
  have heta4 : P.eta ≤ 1 / 4 := by
    unfold Params.eta
    linarith [P.hε1]
  have htheta0 : 0 ≤ P.epsPrime / 4 :=
    div_nonneg P.epsPrime_pos.le (by norm_num)
  have hloss : P.epsPrime / 4 + P.epsPrime / 4 ≤ 1 / 4 := by
    unfold Params.epsPrime
    linarith [P.hε1]
  letI : IsProbabilityMeasure mu :=
    (kv97Sampler_polyHybridCanonical atoms phi eps delta
      h_eps_pos h_eps_le hn hphi hvol).isProbContLaw i
  have htv : Arlib.TVLe mu (Arlib.uniformOn volume K)
      (ENNReal.ofReal ((P.epsPrime / 4) / (volume K).toReal)) := by
    simpa [mu, K, Am, bv, P, div_div] using
      (tvLe_polyHybridCanonical atoms phi eps delta
        h_eps_pos h_eps_le hn hphi hvol i)
  have henum : ∀ z,
      Arlib.KV97.latEmb n z ∈ latticeScale rho0 • region M0 i.val ↔
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
        P.epsPrime / 4 := by
    intro j
    have hjbody : Arlib.KV97.latEmb n j.1 ∈ K0 := by
      rw [hbody]
      exact j.2
    have h := escape_of_mem_body (eps := P.epsPrime) Am bv P.hr
      (by simpa [J] using hfac) hjbody
    have hexp := Arlib.KV97.exp_cOf P.epsPrime_pos (by
      unfold Params.epsPrime
      linarith [P.hε1])
    simpa [K, hexp] using h
  exact Ttc.KV97TVAcceptance.one_eighth_le_roundedMeasure_integerAcceptance_of_tvLe
    mu M0 rho0 i.val Am bv
    (latticeScale rho0 • algCen atoms phi eps delta i)
    (latticeScale rho0 * algGamma atoms phi eps delta)
    (Arlib.KV97.cOf P.epsPrime) P.r (P.epsPrime / 4) (P.epsPrime / 4) P.eta
    (fun j : Z ↦ j.1) hgamma Arlib.KV97.cOf_nonneg hball hfin heta0 heta4
    htheta0 hloss htv hK0 hKtop hlattice hthin Subtype.val_injective henum hesc

/-- Semantic hybrid TTC accuracy with the sampler certificate fully discharged. -/
theorem polyHybridKernel_accuracy_canonical
    (h_eps_pos : 0 < eps) (h_eps_le : eps ≤ 1)
    (h_delta_pos : 0 < delta) (h_delta_le : delta ≤ 1) (hn : 1 ≤ n)
    (hphi : phi.IsPositive) (hvol : 0 < volSol (atomSet atoms) phi)
    (V : VolumeAlgorithm n) :
    letI := V.mΩ
    1 - delta ≤
      ((V.μ.compProd (polyHybridKernel atoms phi eps delta V
        (canonicalHybridInnerRadius atoms phi eps delta)
        (canonicalHybridOuterRadius atoms phi eps delta)
        (canonicalHybridStep atoms phi eps delta)
        (canonicalHybridWarm atoms phi eps delta)
        (canonicalHybridStart atoms phi eps delta)))
        (Ttc.CostedTTCPlugin.idealPolyAccuracyEvent
          (atoms := atoms) (phi := phi) (eps := eps) (delta := delta) V)).toReal :=
  polyHybridKernel_accuracy atoms phi eps delta h_eps_pos h_eps_le h_delta_pos
    h_delta_le hn hphi hvol V
    (canonicalHybridInnerRadius atoms phi eps delta)
    (canonicalHybridOuterRadius atoms phi eps delta)
    (canonicalHybridStep atoms phi eps delta)
    (canonicalHybridWarm atoms phi eps delta)
    (canonicalHybridStart atoms phi eps delta)
    (kv97Sampler_polyHybridCanonical atoms phi eps delta h_eps_pos h_eps_le hn hphi hvol)

#print axioms kv97Sampler_polyHybridCanonical
#print axioms tvLe_polyHybridCanonical
#print axioms one_eighth_le_roundedMeasure_polyHybridCanonical
#print axioms polyHybridKernel_accuracy_canonical

end Ttc.ConcreteHybridCanonicalOwnerPoly

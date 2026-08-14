import Ttc.Exec.PolyAccuracy

/-!
# Polynomial TTC accuracy for an arbitrary certified lattice sampler

The legacy `polyRates` fixes the old plain hit-and-run law.  This file records
the sampler-parametric form of the same proof, without changing that legacy
definition or theorem.
-/

namespace Ttc

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal BigOperators Classical

variable {A : Type*} {n : Nat}

/-- The polynomial TTC rates, with the discrete cube sampler exposed as a
parameter. -/
noncomputable def polyRatesWith (atoms : A → LinAtom n) (phi : BForm A)
    (eps delta : Real) (V : VolumeAlgorithm n) (omega : V.Ω)
    (sampD : Cube A → Space n → Real) :
    Fin (algIndex atoms phi eps delta) → Real :=
  rates (atomSet (algAtoms atoms phi eps delta)) (preprocess atoms phi)
    (toDNFd (preprocess atoms phi)) (algPrec atoms phi eps delta)
    sampD (polyVol atoms phi eps delta V omega)

set_option maxHeartbeats 1000000 in
/-- The regime lower bound for any sampler carrying the same `KV97Sampler`
certificate used by the generic TTC theorem. -/
theorem big_polyRatesWith
    (atoms : A → LinAtom n) (phi : BForm A) (eps delta : Real)
    (hε0 : 0 < eps) (hε1 : eps ≤ 1) (hn : 1 ≤ n)
    (hphi : phi.IsPositive) (hpos : 0 < volSol (atomSet atoms) phi)
    (V : VolumeAlgorithm n)
    (sampD : Cube A → Space n → Real)
    (sampler : KV97Sampler A n (atomSet (algAtoms atoms phi eps delta))
      (toDNFd (preprocess atoms phi)) (algPrec atoms phi eps delta)
      (algBlock atoms phi eps delta).epsPrime sampD) :
    ∀ omega ∈ polyGood atoms phi eps delta V,
      (1 - (algBlock atoms phi eps delta).epsPrime) *
          (algBlock atoms phi eps delta).thresh / 8 ≤
        ∑ s, polyRatesWith atoms phi eps delta V omega sampD s := by
  intro omega homega
  have hbddP : Bornology.IsBounded
      (sol (atomSet atoms) (preprocess atoms phi)) :=
    preprocess_bdd atoms phi hphi hpos
  have hvol : (algBlock atoms phi eps delta).thresh / 4 ≤
      volSol (atomSet (algAtoms atoms phi eps delta)) (preprocess atoms phi) :=
    hvol_scaled atoms (preprocess atoms phi) eps delta hε0 hε1 hn
      (preprocess_isPositive atoms phi) hbddP
      (gammaOf_pos_of_interior (atomSet atoms)
        (toDNFd_ne_nil (preprocess_isPositive atoms phi))
        (preprocess_int atoms phi hphi hpos))
      (autoCen atoms (preprocess atoms phi))
      (ball_subset_cenOf (atomSet atoms) (toDNFd (preprocess atoms phi)))
  have hvolLo : ∀ i : {c : Cube A // c ∈ toDNFd (preprocess atoms phi)},
      (1 - (algBlock atoms phi eps delta).epsPrime) *
          (volume (region (atomSet (algAtoms atoms phi eps delta)) i.val)).toReal ≤
        polyVol atoms phi eps delta V omega i.val := fun i ↦
    (volOfAlg_mem_relErr V (atomSet (algAtoms atoms phi eps delta))
      (toDNFd (preprocess atoms phi)) (algCen atoms phi eps delta)
      (algGamma atoms phi eps delta) (algBlock atoms phi eps delta).epsPrime
      (algBlock atoms phi eps delta).deltaPrime homega i.val i.property).1
  have hPr : (algBlock atoms phi eps delta).r =
      (Nat.card (FacetIndex (toDNFd (preprocess atoms phi))) : Real) :=
    ttcBlock_r atoms phi eps delta hε0 hε1 hn hphi hpos
  have hPm : (algBlock atoms phi eps delta).m = ttcNumCubes atoms phi :=
    ttcBlock_m atoms phi eps delta hε0 hε1 hn hphi hpos
  exact big_of_volume_generic (algAtoms atoms phi eps delta) (toDNFd_isDNFOf _)
    (toDNFd_isPositive (preprocess_isPositive atoms phi))
    (algBlock atoms phi eps delta)
    (ttcBlock_n atoms phi eps delta hε0 hε1 hn hphi hpos)
    (by rw [hPm, ← ttcNumCubes_eq_card atoms phi]) (by rw [hPr])
    (normal_ne_zero_of_coeff_ne_zero (preprocess_coeff atoms phi hphi hpos))
    (algAtoms_bdd atoms phi eps delta hε0 hε1 hn hphi hpos)
    (algCen atoms phi eps delta)
    (algGamma_pos_of_isPositive atoms phi eps delta hphi hpos)
    (ball_subset_algCen atoms phi eps delta) rfl hvol sampler hvolLo

set_option maxHeartbeats 1000000 in
/-- Sampler-parametric form of `lintegral_ttcPolyRun_ge`.  The algorithmic
output is unchanged; only the level-zero trajectory rates use `sampD`. -/
theorem lintegral_ttcPolyRun_ge_withSampler
    (atoms : A → LinAtom n) (phi : BForm A) (eps delta : Real)
    (hε0 : 0 < eps) (hε1 : eps ≤ 1) (hδ0 : 0 < delta)
    (hδ1 : delta ≤ 1) (hn : 1 ≤ n)
    (hphi : phi.IsPositive) (hpos : 0 < volSol (atomSet atoms) phi)
    (V : VolumeAlgorithm n)
    (sampD : Cube A → Space n → Real)
    (sampler : KV97Sampler A n (atomSet (algAtoms atoms phi eps delta))
      (toDNFd (preprocess atoms phi)) (algPrec atoms phi eps delta)
      (algBlock atoms phi eps delta).epsPrime sampD)
    (big : ∀ omega ∈ polyGood atoms phi eps delta V,
      (1 - (algBlock atoms phi eps delta).epsPrime) *
          (algBlock atoms phi eps delta).thresh / 8 ≤
        ∑ s, polyRatesWith atoms phi eps delta V omega sampD s) :
    1 - delta ≤
      letI := V.mΩ
      (∫⁻ omega, trajLaw (polyRatesWith atoms phi eps delta V omega sampD)
          {t | ttcPolyRun atoms phi eps delta V omega t ∈
            relErr eps (volSol (atomSet atoms) phi)} ∂V.μ).toReal := by
  classical
  letI := V.mΩ
  haveI := V.isProb
  have hbdd : Bornology.IsBounded
      (sol (atomSet (algAtoms atoms phi eps delta)) (preprocess atoms phi)) :=
    algAtoms_bdd atoms phi eps delta hε0 hε1 hn hphi hpos
  have hisD : IsDNFOf (toDNFd (preprocess atoms phi)) (preprocess atoms phi) :=
    toDNFd_isDNFOf _
  have hisP : DNF.IsPositive (toDNFd (preprocess atoms phi)) :=
    toDNFd_isPositive (preprocess_isPositive atoms phi)
  have hg : 0 < algGamma atoms phi eps delta :=
    algGamma_pos_of_isPositive atoms phi eps delta hphi hpos
  have hball := ball_subset_algCen atoms phi eps delta
  have hfin : ∀ i : {c : Cube A // c ∈ toDNFd (preprocess atoms phi)},
      volume (region (atomSet (algAtoms atoms phi eps delta)) i.val) ≠ ⊤ :=
    volume_region_ne_top_of_isBounded hisD hbdd
  have hconv : ∀ i : {c : Cube A // c ∈ toDNFd (preprocess atoms phi)},
      Convex Real (region (atomSet (algAtoms atoms phi eps delta)) i.val) :=
    fun i ↦ convex_region (algAtoms atoms phi eps delta) _
  have hle : HasLatticeEnum (atomSet (algAtoms atoms phi eps delta))
      (preprocess atoms phi) (algPrec atoms phi eps delta) :=
    hasLatticeEnum_of_isBounded _ _ _ hbdd
  have heps0 : (0 : Real) < (algBlock atoms phi eps delta).ε :=
    (algBlock atoms phi eps delta).hε0
  have heps1 : (algBlock atoms phi eps delta).ε ≤ 1 :=
    (algBlock atoms phi eps delta).hε1
  have hep1 : (algBlock atoms phi eps delta).epsPrime < 1 := by
    unfold Params.epsPrime
    linarith
  have hPm : (algBlock atoms phi eps delta).m = ttcNumCubes atoms phi :=
    ttcBlock_m atoms phi eps delta hε0 hε1 hn hphi hpos
  have hPr : (algBlock atoms phi eps delta).r =
      (Nat.card (FacetIndex (toDNFd (preprocess atoms phi))) : Real) :=
    ttcBlock_r atoms phi eps delta hε0 hε1 hn hphi hpos
  have hmlen : ((toDNFd (preprocess atoms phi)).length : Real) ≤
      (algBlock atoms phi eps delta).m := by
    rw [hPm]
    exact le_rfl
  have hcubes : (Nat.card {c : Cube A // c ∈ toDNFd (preprocess atoms phi)} : Real) ≤
      (algBlock atoms phi eps delta).m := by
    rw [hPm, ← ttcNumCubes_eq_card atoms phi]
  have hfacets : (Nat.card (FacetIndex (toDNFd (preprocess atoms phi))) : Real) ≤
      (algBlock atoms phi eps delta).r := by rw [hPr]
  have hδ0' : (0 : Real) < 4 * delta / 5 := by linarith
  have hδ1' : (4 : Real) * delta / 5 ≤ 1 := by linarith
  have hkey := volume_estimate_joint eps (4 * delta / 5) hε0 hε1 hδ0' hδ1'
    (algAtoms atoms phi eps delta) (atomSet (algAtoms atoms phi eps delta)) rfl
    (preprocess atoms phi) toDNFd hisD hisP (algBlock atoms phi eps delta)
    (ttcBlock_eps atoms phi eps delta hε0 hε1 hn hphi hpos)
    (ttcBlock_delta atoms phi eps delta hε0 hε1 hn hphi hpos)
    (ttcBlock_n atoms phi eps delta hε0 hε1 hn hphi hpos)
    hcubes hfacets
    (normal_ne_zero_of_coeff_ne_zero (preprocess_coeff atoms phi hphi hpos))
    (algCen atoms phi eps delta) (algGamma atoms phi eps delta) hg hball hfin
    (algPrec atoms phi eps delta) rfl _ rfl (algIndex atoms phi eps delta)
    (algEnum atoms phi eps delta) (latticeEnum_injective _ _ _)
    (fun s ↦ latticeEnum_mem hle s) (latticeEnum_onto hle) V
    (fun omega ↦ polyRatesWith atoms phi eps delta V omega sampD)
    (fun omega ↦ polyVol atoms phi eps delta V omega) sampD sampler
    (fun omega s ↦ theta_eq_rates hisD hle _ _ s)
    (coverOfRegion (atomSet (algAtoms atoms phi eps delta)))
    (algMem atoms phi eps delta) (memPtOfRegion_spec _ _ _)
    (fun s i ↦ coverOfRegion_memPtOfRegion _ _ s i)
    (fun omega t i j N hi ↦
      gen_mem_of_geometry (algAtoms atoms phi eps delta) hisD hisP hbdd
        (preprocess_coeff atoms phi hphi hpos) (algBlock atoms phi eps delta)
        (ttcBlock_n atoms phi eps delta hε0 hε1 hn hphi hpos) hfacets
        (algCen atoms phi eps delta) hg hball rfl
        (polyVol atoms phi eps delta V omega) t i j N hi)
    (fun omega i hi ↦ volOfAlg_eq V (atomSet (algAtoms atoms phi eps delta))
      (toDNFd (preprocess atoms phi)) (algCen atoms phi eps delta)
      (algGamma atoms phi eps delta) (algBlock atoms phi eps delta).epsPrime
      (algBlock atoms phi eps delta).deltaPrime omega i hi)
    (polyGood atoms phi eps delta V) (measurableSet_volGood V _ _ _ _ _)
    (measure_volGood_ge_of_length V (atomSet (algAtoms atoms phi eps delta))
      (toDNFd (preprocess atoms phi)) (algBlock atoms phi eps delta)
      (ttcBlock_delta atoms phi eps delta hε0 hε1 hn hphi hpos) hδ0' hδ1' hg
      (algCen atoms phi eps delta) hball hconv hfin hmlen)
    (fun omega homega ↦ volOfAlg_mem_relErr V
      (atomSet (algAtoms atoms phi eps delta)) (toDNFd (preprocess atoms phi))
      (algCen atoms phi eps delta) (algGamma atoms phi eps delta)
      (algBlock atoms phi eps delta).epsPrime (algBlock atoms phi eps delta).deltaPrime
      homega)
    (fun omega homega ↦ volOfAlg_pos V
      (atomSet (algAtoms atoms phi eps delta)) (toDNFd (preprocess atoms phi))
      (algCen atoms phi eps delta) hg hep1 hball hfin
      homega)
    big
  rw [volSol_algAtoms_of_isPositive atoms phi eps delta hphi hpos] at hkey
  simp only [setOf_mem_relErr_div _ (pow_pos (algScale_pos_uncond atoms phi eps delta) n)]
    at hkey
  exact le_trans (by linarith) hkey

theorem lintegral_ttcPolyRun_ge_withSampler_closedBig
    (atoms : A → LinAtom n) (phi : BForm A) (eps delta : Real)
    (hε0 : 0 < eps) (hε1 : eps ≤ 1) (hδ0 : 0 < delta)
    (hδ1 : delta ≤ 1) (hn : 1 ≤ n)
    (hphi : phi.IsPositive) (hpos : 0 < volSol (atomSet atoms) phi)
    (V : VolumeAlgorithm n)
    (sampD : Cube A → Space n → Real)
    (sampler : KV97Sampler A n (atomSet (algAtoms atoms phi eps delta))
      (toDNFd (preprocess atoms phi)) (algPrec atoms phi eps delta)
      (algBlock atoms phi eps delta).epsPrime sampD) :
    1 - delta ≤
      letI := V.mΩ
      (∫⁻ omega, trajLaw (polyRatesWith atoms phi eps delta V omega sampD)
          {t | ttcPolyRun atoms phi eps delta V omega t ∈
            relErr eps (volSol (atomSet atoms) phi)} ∂V.μ).toReal :=
  lintegral_ttcPolyRun_ge_withSampler atoms phi eps delta hε0 hε1 hδ0 hδ1 hn hphi
    hpos V sampD sampler
    (big_polyRatesWith atoms phi eps delta hε0 hε1 hn hphi hpos V sampD sampler)

#print axioms polyRatesWith
#print axioms big_polyRatesWith
#print axioms lintegral_ttcPolyRun_ge_withSampler
#print axioms lintegral_ttcPolyRun_ge_withSampler_closedBig

end Ttc

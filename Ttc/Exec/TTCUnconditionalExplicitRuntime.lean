import Ttc.Exec.TTCOperationalPaperBridge
import Ttc.Exec.CVSourceTheorem11Arithmetic

/-!
# An unconditional explicit operational TTC runtime envelope

`TTCOperationalPaperBridge` compares the operational counters with the coefficient-one
display in `analysis.tex` through three local inequalities.  Those inequalities cannot
hold uniformly: the source CV price contains its cutoff/amplification constants and
logarithms, while the paper suppresses them.

This file removes all three comparison hypotheses by taking finite suprema of the actual
per-cube quantities.  The resulting bound has the same decomposition as the paper,

`number of cubes * (volume-call cap + rate cap * endpoint-inspection cap)`,

but retains every constant, logarithm, warmness term, radius, and volume occurring in the
implemented oracles.  In particular, no proposed coefficient-one polynomial estimate is
silently substituted for an operational counter.
-/

namespace Ttc.TTCUnconditionalExplicitRuntime

open MeasureTheory ProbabilityTheory Set
open Ttc.CVSourcePolynomialCutoffCapstone
open Ttc.CVSourceTheorem11Arithmetic
open Ttc.ConcreteHybridCanonicalOwnerPoly
open Ttc.CostedCanonicalOwnerTTCPlugin
open Ttc.TTCSourceSharpOperationalFinal
open Ttc.TTCSourceSharpOperationalTheorem
open scoped ENNReal BigOperators Classical

variable {A : Type*} {n : Nat}

/-- The complete, honest envelope for one specified source-CV volume call. -/
noncomputable def sourceCallQueryEnvelope
    (atoms : A → LinAtom n) (phi : BForm A) (eps delta : Real)
    (runtimeConstant : Real) (radialR : Set (Space n) → Real)
    (j : Fin (toDNFd (preprocess atoms phi)).length) : ENNReal :=
  ENNReal.ofReal
    (sourceAmplifiedQueryEnvelope runtimeConstant n
      (radialR
        (roundBody
          (algCen atoms phi eps delta
            ⟨(toDNFd (preprocess atoms phi)).get j,
              List.get_mem (toDNFd (preprocess atoms phi)) j⟩)
          (algGamma atoms phi eps delta)
          (region (atomSet (algAtoms atoms phi eps delta))
            ((toDNFd (preprocess atoms phi)).get j))))
      (algBlock atoms phi eps delta).epsPrime
      (algBlock atoms phi eps delta).deltaPrime)

/-- A deterministic uniform volume-call price.  It is a finite supremum, so it includes
the exact source cutoff factor `20`, median amplification `8*log(1/p)+2`, all clipped
logarithms, the call's radial moment, and its `epsPrime^-2` dependence. -/
noncomputable def sourceCallQueryCap
    (atoms : A → LinAtom n) (phi : BForm A) (eps delta : Real)
    (runtimeConstant : Real) (radialR : Set (Space n) → Real) : ENNReal :=
  Finset.univ.sup fun j : Fin (toDNFd (preprocess atoms phi)).length ↦
    sourceCallQueryEnvelope atoms phi eps delta runtimeConstant radialR j

/-- The largest squared radial parameter among TTC's actual rounded volume bodies.  It is
an `NNReal` finite supremum, avoiding both an empty-DNF side condition and an extra factor
of the cube count. -/
noncomputable def sourceRadialSquaredCap
    (atoms : A → LinAtom n) (phi : BForm A) (eps delta : Real)
    (radialR : Set (Space n) → Real) : NNReal :=
  Finset.univ.sup fun j : Fin (toDNFd (preprocess atoms phi)).length ↦
    ((radialR
      (roundBody
        (algCen atoms phi eps delta
          ⟨(toDNFd (preprocess atoms phi)).get j,
            List.get_mem (toDNFd (preprocess atoms phi)) j⟩)
        (algGamma atoms phi eps delta)
        (region (atomSet (algAtoms atoms phi eps delta))
          ((toDNFd (preprocess atoms phi)).get j)))) ^ 2).toNNReal

/-- A deterministic `Threshold` for the clipped Poisson intensities.  Unlike the paper's
closed asymptotic symbol, this is definitionally computed from the actual caps and hence
dominates them without a geometric side condition. -/
noncomputable def canonicalRateThreshold
    (atoms : A → LinAtom n) (phi : BForm A) (eps delta : Real) : ENNReal :=
  Finset.univ.sup fun i : CubeIndex atoms phi ↦
    (polyGoodRateCap atoms phi eps delta i : ENNReal)

/-- A closed, cube-free rate threshold obtained from geometry: each cube region is inside
the preprocessed solution set, whose volume is exactly `algScale^n` times the user's
original solution volume. -/
noncomputable def canonicalClosedRateThreshold
    (atoms : A → LinAtom n) (phi : BForm A) (eps delta : Real) : ENNReal :=
  ENNReal.ofReal
    ((1 + (algBlock atoms phi eps delta).epsPrime) *
      (algScale atoms phi eps delta ^ n * volSol (atomSet atoms) phi))

/-- The deterministic uniform price of one canonical hybrid endpoint, including all
continuous-walk facet inspections, low-dimensional fallback terms, and the factor-eight
KV97 rejection overhead. -/
noncomputable def canonicalEndpointInspectionCap
    (atoms : A → LinAtom n) (phi : BForm A) (eps delta : Real) : ENNReal :=
  Finset.univ.sup fun i : CubeIndex atoms phi ↦
    canonicalHybridSamplerQueryBound atoms phi eps delta i

/-- Unconditional paper-shaped operational envelope.  This is explicit at the run's own
data and makes no `rho`, `rMax`, or coefficient-one comparison assumption. -/
noncomputable def explicitOperationalRuntimeEnvelope
    (atoms : A → LinAtom n) (phi : BForm A) (eps delta : Real)
    (runtimeConstant : Real) (radialR : Set (Space n) → Real) : ENNReal :=
  ((toDNFd (preprocess atoms phi)).length : ENNReal) *
    (sourceCallQueryCap atoms phi eps delta runtimeConstant radialR +
      canonicalRateThreshold atoms phi eps delta *
        canonicalEndpointInspectionCap atoms phi eps delta)

theorem sourceCallQueryEnvelope_le_cap
    (atoms : A → LinAtom n) (phi : BForm A) (eps delta : Real)
    (runtimeConstant : Real) (radialR : Set (Space n) → Real)
    (j : Fin (toDNFd (preprocess atoms phi)).length) :
    sourceCallQueryEnvelope atoms phi eps delta runtimeConstant radialR j ≤
      sourceCallQueryCap atoms phi eps delta runtimeConstant radialR := by
  unfold sourceCallQueryCap
  exact Finset.le_sup (Finset.mem_univ j)

theorem sourceCall_radial_sq_le_cap
    (atoms : A → LinAtom n) (phi : BForm A) (eps delta : Real)
    (radialR : Set (Space n) → Real)
    (j : Fin (toDNFd (preprocess atoms phi)).length) :
    (radialR
      (roundBody
        (algCen atoms phi eps delta
          ⟨(toDNFd (preprocess atoms phi)).get j,
            List.get_mem (toDNFd (preprocess atoms phi)) j⟩)
        (algGamma atoms phi eps delta)
        (region (atomSet (algAtoms atoms phi eps delta))
          ((toDNFd (preprocess atoms phi)).get j)))) ^ 2 ≤
      (sourceRadialSquaredCap atoms phi eps delta radialR : Real) := by
  let R := radialR
    (roundBody
      (algCen atoms phi eps delta
        ⟨(toDNFd (preprocess atoms phi)).get j,
          List.get_mem (toDNFd (preprocess atoms phi)) j⟩)
      (algGamma atoms phi eps delta)
      (region (atomSet (algAtoms atoms phi eps delta))
        ((toDNFd (preprocess atoms phi)).get j)))
  have hnn : (R ^ 2).toNNReal ≤ sourceRadialSquaredCap atoms phi eps delta radialR := by
    unfold sourceRadialSquaredCap
    exact Finset.le_sup
      (f := fun k : Fin (toDNFd (preprocess atoms phi)).length ↦
        ((radialR
          (roundBody
            (algCen atoms phi eps delta
              ⟨(toDNFd (preprocess atoms phi)).get k,
                List.get_mem (toDNFd (preprocess atoms phi)) k⟩)
            (algGamma atoms phi eps delta)
            (region (atomSet (algAtoms atoms phi eps delta))
              ((toDNFd (preprocess atoms phi)).get k)))) ^ 2).toNNReal)
      (Finset.mem_univ j)
  have hcast : ((R ^ 2).toNNReal : Real) ≤
      (sourceRadialSquaredCap atoms phi eps delta radialR : Real) := by
    exact_mod_cast hnn
  rw [Real.coe_toNNReal _ (sq_nonneg R)] at hcast
  exact hcast

/-- Every actual source-CV call is bounded by the corrected Theorem-1.1
polynomial/polylogarithmic shape at the run's maximum squared radial scale. -/
theorem sourceCallQueryEnvelope_le_cvShape
    (atoms : A → LinAtom n) (phi : BForm A) (eps delta : Real)
    (runtimeConstant : Real) (radialR : Set (Space n) → Real)
    (hconstant : 0 ≤ runtimeConstant)
    (h_eps_pos : 0 < eps) (h_eps_le : eps ≤ 1)
    (h_delta_pos : 0 < delta) (h_delta_le : delta ≤ 1)
    (hn : 1 ≤ n) (hphi : phi.IsPositive)
    (hvol : 0 < volSol (atomSet atoms) phi)
    (j : Fin (toDNFd (preprocess atoms phi)).length) :
    sourceCallQueryEnvelope atoms phi eps delta runtimeConstant radialR j ≤
      ENNReal.ofReal
        ((200 * (runtimeConstant + 1)) *
          cvComplexityShapeClipped n
            (sourceRadialSquaredCap atoms phi eps delta radialR : Real)
            (algBlock atoms phi eps delta).epsPrime
            (algBlock atoms phi eps delta).deltaPrime) := by
  have heps0 : 0 < (algBlock atoms phi eps delta).epsPrime :=
    algBlock_epsPrime_pos atoms phi eps delta
  have heps1 : (algBlock atoms phi eps delta).epsPrime < 1 := by
    rw [algBlock_epsPrime_eq atoms phi eps delta h_eps_pos h_eps_le hn hphi hvol]
    linarith
  have hp0 : 0 < (algBlock atoms phi eps delta).deltaPrime :=
    algBlock_deltaPrime_pos atoms phi eps delta h_eps_pos h_eps_le hn hphi hvol
      h_delta_pos
  have hp1 : (algBlock atoms phi eps delta).deltaPrime < 1 :=
    lt_of_le_of_lt
      (algBlock_deltaPrime_le_half atoms phi eps delta h_eps_pos h_eps_le hn
        hphi hvol h_delta_le)
      (by norm_num)
  have hR20 : 0 ≤
      (sourceRadialSquaredCap atoms phi eps delta radialR : Real) :=
    NNReal.coe_nonneg _
  unfold sourceCallQueryEnvelope
  apply ENNReal.ofReal_le_ofReal
  exact sourceAmplifiedQueryEnvelope_le_cvComplexityShapeClipped
    hconstant hn hR20
    (sourceCall_radial_sq_le_cap atoms phi eps delta radialR j)
    heps0 heps1 hp0 hp1

theorem sourceCallQueryCap_le_cvShape
    (atoms : A → LinAtom n) (phi : BForm A) (eps delta : Real)
    (runtimeConstant : Real) (radialR : Set (Space n) → Real)
    (hconstant : 0 ≤ runtimeConstant)
    (h_eps_pos : 0 < eps) (h_eps_le : eps ≤ 1)
    (h_delta_pos : 0 < delta) (h_delta_le : delta ≤ 1)
    (hn : 1 ≤ n) (hphi : phi.IsPositive)
    (hvol : 0 < volSol (atomSet atoms) phi) :
    sourceCallQueryCap atoms phi eps delta runtimeConstant radialR ≤
      ENNReal.ofReal
        ((200 * (runtimeConstant + 1)) *
          cvComplexityShapeClipped n
            (sourceRadialSquaredCap atoms phi eps delta radialR : Real)
            (algBlock atoms phi eps delta).epsPrime
            (algBlock atoms phi eps delta).deltaPrime) := by
  unfold sourceCallQueryCap
  apply Finset.sup_le
  intro j hj
  exact sourceCallQueryEnvelope_le_cvShape atoms phi eps delta runtimeConstant
    radialR hconstant h_eps_pos h_eps_le h_delta_pos h_delta_le hn hphi hvol j

theorem polyGoodRateCap_le_canonicalRateThreshold
    (atoms : A → LinAtom n) (phi : BForm A) (eps delta : Real)
    (i : CubeIndex atoms phi) :
    (polyGoodRateCap atoms phi eps delta i : ENNReal) ≤
      canonicalRateThreshold atoms phi eps delta := by
  unfold canonicalRateThreshold
  exact Finset.le_sup
    (f := fun j : CubeIndex atoms phi ↦
      (polyGoodRateCap atoms phi eps delta j : ENNReal))
    (Finset.mem_univ i)

/-- The closed threshold dominates every actual clipped Poisson intensity cap. -/
theorem polyGoodRateCap_le_canonicalClosedRateThreshold
    (atoms : A → LinAtom n) (phi : BForm A) (eps delta : Real)
    (h_eps_pos : 0 < eps) (h_eps_le : eps ≤ 1) (hn : 1 ≤ n)
    (hphi : phi.IsPositive) (hvol : 0 < volSol (atomSet atoms) phi)
    (i : CubeIndex atoms phi) :
    (polyGoodRateCap atoms phi eps delta i : ENNReal) ≤
      canonicalClosedRateThreshold atoms phi eps delta := by
  have hbdd : Bornology.IsBounded
      (sol (atomSet (algAtoms atoms phi eps delta)) (preprocess atoms phi)) :=
    isBounded_sol_algAtoms atoms phi eps delta h_eps_pos h_eps_le hn hphi hvol
  have htop : volume
      (sol (atomSet (algAtoms atoms phi eps delta)) (preprocess atoms phi)) ≠ ⊤ :=
    hbdd.measure_lt_top.ne
  have hregion :
      (volume
        (region (atomSet (algAtoms atoms phi eps delta)) i.val)).toReal ≤
        algScale atoms phi eps delta ^ n * volSol (atomSet atoms) phi := by
    have hmono := ENNReal.toReal_mono htop
      (measure_mono (region_subset_sol (toDNFd_isDNFOf (preprocess atoms phi)) i.property))
    rw [← volSol_algAtoms atoms phi eps delta h_eps_pos h_eps_le hn hphi hvol]
    exact hmono
  have hfactor : 0 ≤ 1 + (algBlock atoms phi eps delta).epsPrime := by
    have hp := (algBlock atoms phi eps delta).epsPrime_pos
    linarith
  have hraw : 0 ≤
      (1 + (algBlock atoms phi eps delta).epsPrime) *
        (volume
          (region (atomSet (algAtoms atoms phi eps delta)) i.val)).toReal :=
    mul_nonneg hfactor ENNReal.toReal_nonneg
  unfold polyGoodRateCap canonicalClosedRateThreshold
  rw [ENNReal.coe_nnreal_eq, Real.coe_toNNReal _ hraw]
  exact ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left hregion hfactor)

theorem canonicalRateThreshold_le_closed
    (atoms : A → LinAtom n) (phi : BForm A) (eps delta : Real)
    (h_eps_pos : 0 < eps) (h_eps_le : eps ≤ 1) (hn : 1 ≤ n)
    (hphi : phi.IsPositive) (hvol : 0 < volSol (atomSet atoms) phi) :
    canonicalRateThreshold atoms phi eps delta ≤
      canonicalClosedRateThreshold atoms phi eps delta := by
  unfold canonicalRateThreshold
  apply Finset.sup_le
  intro i hi
  exact polyGoodRateCap_le_canonicalClosedRateThreshold atoms phi eps delta
    h_eps_pos h_eps_le hn hphi hvol i

theorem canonicalHybridSamplerQueryBound_le_endpointCap
    (atoms : A → LinAtom n) (phi : BForm A) (eps delta : Real)
    (i : CubeIndex atoms phi) :
    canonicalHybridSamplerQueryBound atoms phi eps delta i ≤
      canonicalEndpointInspectionCap atoms phi eps delta := by
  unfold canonicalEndpointInspectionCap
  exact Finset.le_sup (Finset.mem_univ i)

/-- The rejection wrapper alone costs eight inspections in the displayed operational
envelope.  Thus a coefficient-one comparison with `rMax*n^5*rho^2` necessarily requires
that paper expression to be at least eight; it cannot be an unconditional inequality for
arbitrary normalizing parameters. -/
theorem eight_le_canonicalHybridSamplerQueryBound
    (atoms : A → LinAtom n) (phi : BForm A) (eps delta : Real)
    (i : CubeIndex atoms phi) :
    (8 : ENNReal) ≤ canonicalHybridSamplerQueryBound atoms phi eps delta i := by
  unfold canonicalHybridSamplerQueryBound
  dsimp only
  calc
    (8 : ENNReal) = 8 * 1 := by norm_num
    _ ≤ 8 *
        (ENNReal.ofReal
            (hybridTransitionBound n
              (canonicalHybridInnerRadius atoms phi eps delta i)
              (canonicalHybridOuterRadius atoms phi eps delta i)
              (canonicalHybridStep atoms phi eps delta i)
              (canonicalHybridWarm atoms phi eps delta i)
              ((algBlock atoms phi eps delta).epsPrime /
                (4 * (volume
                  (Arlib.KV97.inflated
                    (canonAm (algAtoms atoms phi eps delta) (D atoms phi) i)
                    (canonBv (algAtoms atoms phi eps delta) (D atoms phi)
                      (latticeScale (rho atoms phi eps delta)) i)
                    (Arlib.KV97.cOf (algBlock atoms phi eps delta).epsPrime)
                    (algBlock atoms phi eps delta).r)).toReal))) *
              Ttc.ConcreteHybridExpectedQuerySampler.hybridStepInspectionBound n
                (Nat.card (FacetIndex (D atoms phi))) + 1) := by
      exact mul_le_mul_right (le_add_left le_rfl) 8

theorem canonicalEndpoint_paperComparison_forces_eight
    (atoms : A → LinAtom n) (phi : BForm A) (eps delta : Real)
    (rho rMax : Real) (i : CubeIndex atoms phi)
    (hprice : canonicalHybridSamplerQueryBound atoms phi eps delta i ≤
      ENNReal.ofReal (rMax * (n : Real) ^ 5 * rho ^ 2)) :
    (8 : ENNReal) ≤ ENNReal.ofReal (rMax * (n : Real) ^ 5 * rho ^ 2) :=
  (eight_le_canonicalHybridSamplerQueryBound atoms phi eps delta i).trans hprice

theorem canonicalHybridSamplerQueryBound_ne_top
    (atoms : A → LinAtom n) (phi : BForm A) (eps delta : Real)
    (i : CubeIndex atoms phi) :
    canonicalHybridSamplerQueryBound atoms phi eps delta i ≠ ⊤ := by
  unfold canonicalHybridSamplerQueryBound
  dsimp only
  apply ENNReal.mul_ne_top
  · norm_num
  · apply ENNReal.add_ne_top.mpr
    constructor
    · apply ENNReal.mul_ne_top
      · simp
      · unfold Ttc.ConcreteHybridExpectedQuerySampler.hybridStepInspectionBound
        split
        · apply ENNReal.mul_ne_top
          · simp
          · exact ENNReal.natCast_ne_top _
        · simp
    · simp

/-- The uniform endpoint cap is a finite explicit number, rather than a qualitative
polynomial-time assertion. -/
theorem canonicalEndpointInspectionCap_ne_top
    (atoms : A → LinAtom n) (phi : BForm A) (eps delta : Real) :
    canonicalEndpointInspectionCap atoms phi eps delta ≠ ⊤ := by
  unfold canonicalEndpointInspectionCap
  apply ne_of_lt
  rw [Finset.sup_lt_iff (by simp : (⊥ : ENNReal) < ⊤)]
  intro i hi
  exact (lt_top_iff_ne_top).2
    (canonicalHybridSamplerQueryBound_ne_top atoms phi eps delta i)

/-- The exact source sum is bounded by the number of calls times the honest uniform call
cap.  This is the premise-free replacement for `hvolumeCall`. -/
theorem ttcSourceVolumeQueryEnvelope_le_explicitCap
    (atoms : A → LinAtom n) (phi : BForm A) (eps delta : Real)
    (runtimeConstant : Real) (radialR : Set (Space n) → Real) :
    ttcSourceVolumeQueryEnvelope atoms phi eps delta runtimeConstant radialR ≤
      ((toDNFd (preprocess atoms phi)).length : ENNReal) *
        sourceCallQueryCap atoms phi eps delta runtimeConstant radialR := by
  unfold ttcSourceVolumeQueryEnvelope
  change (∑ j : Fin (toDNFd (preprocess atoms phi)).length,
      sourceCallQueryEnvelope atoms phi eps delta runtimeConstant radialR j) ≤ _
  calc
    _ ≤ ∑ _j : Fin (toDNFd (preprocess atoms phi)).length,
          sourceCallQueryCap atoms phi eps delta runtimeConstant radialR := by
      apply Finset.sum_le_sum
      intro j hj
      exact sourceCallQueryEnvelope_le_cap atoms phi eps delta runtimeConstant radialR j
    _ = ((toDNFd (preprocess atoms phi)).length : ENNReal) *
          sourceCallQueryCap atoms phi eps delta runtimeConstant radialR := by simp

/-- The complete clipped sampling sum is bounded by cube count times deterministic rate
and endpoint caps.  This simultaneously removes `hcap` and `hprice`. -/
theorem canonicalCappedSampleQueryEnvelope_le_explicitCaps
    (atoms : A → LinAtom n) (phi : BForm A) (eps delta : Real) :
    canonicalCappedSampleQueryEnvelope atoms phi eps delta ≤
      ((toDNFd (preprocess atoms phi)).length : ENNReal) *
        (canonicalRateThreshold atoms phi eps delta *
          canonicalEndpointInspectionCap atoms phi eps delta) := by
  unfold canonicalCappedSampleQueryEnvelope
  calc
    _ ≤ ∑ _i : CubeIndex atoms phi,
          canonicalRateThreshold atoms phi eps delta *
            canonicalEndpointInspectionCap atoms phi eps delta := by
      apply Finset.sum_le_sum
      intro i hi
      exact mul_le_mul
        (polyGoodRateCap_le_canonicalRateThreshold atoms phi eps delta i)
        (canonicalHybridSamplerQueryBound_le_endpointCap atoms phi eps delta i)
        bot_le bot_le
    _ = (Fintype.card (CubeIndex atoms phi) : ENNReal) *
          (canonicalRateThreshold atoms phi eps delta *
            canonicalEndpointInspectionCap atoms phi eps delta) := by simp
    _ = ((toDNFd (preprocess atoms phi)).length : ENNReal) *
          (canonicalRateThreshold atoms phi eps delta *
            canonicalEndpointInspectionCap atoms phi eps delta) := by
      rw [Ttc.TTCOperationalPaperBridge.card_cubeIndex_eq_length]

/-- Both operational counters obey the explicit paper-shaped envelope without any local
comparison premises. -/
theorem operationalEnvelopes_le_explicitRuntime
    (atoms : A → LinAtom n) (phi : BForm A) (eps delta : Real)
    (runtimeConstant : Real) (radialR : Set (Space n) → Real) :
    ttcSourceVolumeQueryEnvelope atoms phi eps delta runtimeConstant radialR +
        canonicalCappedSampleQueryEnvelope atoms phi eps delta ≤
      explicitOperationalRuntimeEnvelope atoms phi eps delta runtimeConstant radialR := by
  unfold explicitOperationalRuntimeEnvelope
  calc
    _ ≤ ((toDNFd (preprocess atoms phi)).length : ENNReal) *
          sourceCallQueryCap atoms phi eps delta runtimeConstant radialR +
        ((toDNFd (preprocess atoms phi)).length : ENNReal) *
          (canonicalRateThreshold atoms phi eps delta *
            canonicalEndpointInspectionCap atoms phi eps delta) :=
      add_le_add
        (ttcSourceVolumeQueryEnvelope_le_explicitCap atoms phi eps delta
          runtimeConstant radialR)
        (canonicalCappedSampleQueryEnvelope_le_explicitCaps atoms phi eps delta)
    _ = ((toDNFd (preprocess atoms phi)).length : ENNReal) *
        (sourceCallQueryCap atoms phi eps delta runtimeConstant radialR +
          canonicalRateThreshold atoms phi eps delta *
            canonicalEndpointInspectionCap atoms phi eps delta) := by
      rw [mul_add]

/-- Closed variant of the unconditional envelope, replacing the finite supremum of rate
caps by the explicit scaled total-volume threshold. -/
noncomputable def explicitClosedOperationalRuntimeEnvelope
    (atoms : A → LinAtom n) (phi : BForm A) (eps delta : Real)
    (runtimeConstant : Real) (radialR : Set (Space n) → Real) : ENNReal :=
  ((toDNFd (preprocess atoms phi)).length : ENNReal) *
    (sourceCallQueryCap atoms phi eps delta runtimeConstant radialR +
      canonicalClosedRateThreshold atoms phi eps delta *
        canonicalEndpointInspectionCap atoms phi eps delta)

/-- Honest polynomial/polylogarithmic TTC envelope after substituting the proved public
CV arithmetic.  The source volume term now has exactly the corrected Theorem-1.1 shape;
the sampling term retains the closed rate threshold and the operational hybrid geometry
cap. -/
noncomputable def cvShapeClosedOperationalRuntimeEnvelope
    (atoms : A → LinAtom n) (phi : BForm A) (eps delta : Real)
    (runtimeConstant : Real) (radialR : Set (Space n) → Real) : ENNReal :=
  ((toDNFd (preprocess atoms phi)).length : ENNReal) *
    (ENNReal.ofReal
        ((200 * (runtimeConstant + 1)) *
          cvComplexityShapeClipped n
            (sourceRadialSquaredCap atoms phi eps delta radialR : Real)
            (algBlock atoms phi eps delta).epsPrime
            (algBlock atoms phi eps delta).deltaPrime) +
      canonicalClosedRateThreshold atoms phi eps delta *
        canonicalEndpointInspectionCap atoms phi eps delta)

theorem explicitOperationalRuntimeEnvelope_le_closed
    (atoms : A → LinAtom n) (phi : BForm A) (eps delta : Real)
    (runtimeConstant : Real) (radialR : Set (Space n) → Real)
    (h_eps_pos : 0 < eps) (h_eps_le : eps ≤ 1) (hn : 1 ≤ n)
    (hphi : phi.IsPositive) (hvol : 0 < volSol (atomSet atoms) phi) :
    explicitOperationalRuntimeEnvelope atoms phi eps delta runtimeConstant radialR ≤
      explicitClosedOperationalRuntimeEnvelope atoms phi eps delta
        runtimeConstant radialR := by
  unfold explicitOperationalRuntimeEnvelope explicitClosedOperationalRuntimeEnvelope
  gcongr
  exact canonicalRateThreshold_le_closed atoms phi eps delta
    h_eps_pos h_eps_le hn hphi hvol

theorem explicitClosedOperationalRuntimeEnvelope_le_cvShape
    (atoms : A → LinAtom n) (phi : BForm A) (eps delta : Real)
    (runtimeConstant : Real) (radialR : Set (Space n) → Real)
    (hconstant : 0 ≤ runtimeConstant)
    (h_eps_pos : 0 < eps) (h_eps_le : eps ≤ 1)
    (h_delta_pos : 0 < delta) (h_delta_le : delta ≤ 1)
    (hn : 1 ≤ n) (hphi : phi.IsPositive)
    (hvol : 0 < volSol (atomSet atoms) phi) :
    explicitClosedOperationalRuntimeEnvelope atoms phi eps delta
        runtimeConstant radialR ≤
      cvShapeClosedOperationalRuntimeEnvelope atoms phi eps delta
        runtimeConstant radialR := by
  unfold explicitClosedOperationalRuntimeEnvelope cvShapeClosedOperationalRuntimeEnvelope
  gcongr
  exact sourceCallQueryCap_le_cvShape atoms phi eps delta runtimeConstant radialR
    hconstant h_eps_pos h_eps_le h_delta_pos h_delta_le hn hphi hvol

/-- Public J-free operational TTC theorem with no `rho`, `rMax`, `Threshold`, per-call,
per-rate, or per-sampler-price conditions.  The only non-input premise is the volume
oracle's common-law certificate; once CV Theorem 1.1 supplies that construction, this
statement becomes the direct unconditional TTC capstone. -/
theorem ttc_volume_estimate_operational_sourceSharp_fullTrajectory_explicitRuntime
    (atoms : A → LinAtom n) (phi : BForm A) (eps delta : Real)
    (runtimeConstant : Real) (radialR : Set (Space n) → Real)
    (Omega : CVAdaptive.VolumeInput n → Type)
    [mOmega : ∀ a, MeasurableSpace (Omega a)]
    (oneLaw : ∀ a, Measure (Omega a))
    (cost : ∀ a, Omega a → ENNReal)
    (value : ∀ a, Omega a → Real)
    (hcert : SourcePublicOneRunCertificates n runtimeConstant radialR
      Omega oneLaw cost value)
    (hconstant : 0 ≤ runtimeConstant)
    (h_eps_pos : 0 < eps) (h_eps_le : eps ≤ 1)
    (h_delta_pos : 0 < delta) (h_delta_le : delta ≤ 1)
    (hn : 1 ≤ n) (hphi : phi.IsPositive)
    (hvol : 0 < volSol (atomSet atoms) phi) :
    let deltaRun := 4 * delta / 5
    letI : NeZero n := ⟨Nat.ne_of_gt hn⟩
    let V := expectedQueryVolumeAlgorithmOfSourceOneRunCertificates n
      runtimeConstant radialR Omega oneLaw cost value hcert
    letI := V.mΩ
    let P := canonicalCappedPolyHybridPlugin atoms phi eps deltaRun V
      h_eps_pos h_eps_le hn hphi hvol
    (1 - delta ≤ (canonicalFullOperationalLaw V P).real
      {r | r.1 ∈ relErr eps (volSol (atomSet atoms) phi)}) ∧
    ((∫⁻ r, r.2 ∂canonicalFullOperationalLaw V P) ≤
      explicitOperationalRuntimeEnvelope atoms phi eps deltaRun
        runtimeConstant radialR) := by
  let deltaRun := 4 * delta / 5
  letI : NeZero n := ⟨Nat.ne_of_gt hn⟩
  let V := expectedQueryVolumeAlgorithmOfSourceOneRunCertificates n
    runtimeConstant radialR Omega oneLaw cost value hcert
  letI := V.mΩ
  let P := canonicalCappedPolyHybridPlugin atoms phi eps deltaRun V
    h_eps_pos h_eps_le hn hphi hvol
  have hmain :=
    ttc_volume_estimate_operational_sourceSharp_fullTrajectory atoms phi eps delta
      runtimeConstant radialR Omega oneLaw cost value hcert hconstant h_eps_pos
      h_eps_le h_delta_pos h_delta_le hn hphi hvol
  refine ⟨hmain.1, hmain.2.trans ?_⟩
  exact operationalEnvelopes_le_explicitRuntime atoms phi eps deltaRun
    runtimeConstant radialR

/-- The same public theorem with the cube-free, closed total-volume `Threshold`. -/
theorem ttc_volume_estimate_operational_sourceSharp_fullTrajectory_closedRuntime
    (atoms : A → LinAtom n) (phi : BForm A) (eps delta : Real)
    (runtimeConstant : Real) (radialR : Set (Space n) → Real)
    (Omega : CVAdaptive.VolumeInput n → Type)
    [mOmega : ∀ a, MeasurableSpace (Omega a)]
    (oneLaw : ∀ a, Measure (Omega a))
    (cost : ∀ a, Omega a → ENNReal)
    (value : ∀ a, Omega a → Real)
    (hcert : SourcePublicOneRunCertificates n runtimeConstant radialR
      Omega oneLaw cost value)
    (hconstant : 0 ≤ runtimeConstant)
    (h_eps_pos : 0 < eps) (h_eps_le : eps ≤ 1)
    (h_delta_pos : 0 < delta) (h_delta_le : delta ≤ 1)
    (hn : 1 ≤ n) (hphi : phi.IsPositive)
    (hvol : 0 < volSol (atomSet atoms) phi) :
    let deltaRun := 4 * delta / 5
    letI : NeZero n := ⟨Nat.ne_of_gt hn⟩
    let V := expectedQueryVolumeAlgorithmOfSourceOneRunCertificates n
      runtimeConstant radialR Omega oneLaw cost value hcert
    letI := V.mΩ
    let P := canonicalCappedPolyHybridPlugin atoms phi eps deltaRun V
      h_eps_pos h_eps_le hn hphi hvol
    (1 - delta ≤ (canonicalFullOperationalLaw V P).real
      {r | r.1 ∈ relErr eps (volSol (atomSet atoms) phi)}) ∧
    ((∫⁻ r, r.2 ∂canonicalFullOperationalLaw V P) ≤
      explicitClosedOperationalRuntimeEnvelope atoms phi eps deltaRun
        runtimeConstant radialR) := by
  let deltaRun := 4 * delta / 5
  have hd0 : 0 < deltaRun := by dsimp [deltaRun]; linarith
  have hd1 : deltaRun ≤ 1 := by dsimp [deltaRun]; linarith
  letI : NeZero n := ⟨Nat.ne_of_gt hn⟩
  let V := expectedQueryVolumeAlgorithmOfSourceOneRunCertificates n
    runtimeConstant radialR Omega oneLaw cost value hcert
  letI := V.mΩ
  let P := canonicalCappedPolyHybridPlugin atoms phi eps deltaRun V
    h_eps_pos h_eps_le hn hphi hvol
  have hmain :=
    ttc_volume_estimate_operational_sourceSharp_fullTrajectory_explicitRuntime
      atoms phi eps delta runtimeConstant radialR Omega oneLaw cost value hcert
      hconstant h_eps_pos h_eps_le h_delta_pos h_delta_le hn hphi hvol
  refine ⟨hmain.1, hmain.2.trans ?_⟩
  exact explicitOperationalRuntimeEnvelope_le_closed atoms phi eps deltaRun
    runtimeConstant radialR h_eps_pos h_eps_le hn hphi hvol

/-- Public capstone with the source call supremum eliminated in favor of the literal
Theorem-1.1 polynomial/polylogarithmic expression. -/
theorem ttc_volume_estimate_operational_sourceSharp_fullTrajectory_cvShapeRuntime
    (atoms : A → LinAtom n) (phi : BForm A) (eps delta : Real)
    (runtimeConstant : Real) (radialR : Set (Space n) → Real)
    (Omega : CVAdaptive.VolumeInput n → Type)
    [mOmega : ∀ a, MeasurableSpace (Omega a)]
    (oneLaw : ∀ a, Measure (Omega a))
    (cost : ∀ a, Omega a → ENNReal)
    (value : ∀ a, Omega a → Real)
    (hcert : SourcePublicOneRunCertificates n runtimeConstant radialR
      Omega oneLaw cost value)
    (hconstant : 0 ≤ runtimeConstant)
    (h_eps_pos : 0 < eps) (h_eps_le : eps ≤ 1)
    (h_delta_pos : 0 < delta) (h_delta_le : delta ≤ 1)
    (hn : 1 ≤ n) (hphi : phi.IsPositive)
    (hvol : 0 < volSol (atomSet atoms) phi) :
    let deltaRun := 4 * delta / 5
    letI : NeZero n := ⟨Nat.ne_of_gt hn⟩
    let V := expectedQueryVolumeAlgorithmOfSourceOneRunCertificates n
      runtimeConstant radialR Omega oneLaw cost value hcert
    letI := V.mΩ
    let P := canonicalCappedPolyHybridPlugin atoms phi eps deltaRun V
      h_eps_pos h_eps_le hn hphi hvol
    (1 - delta ≤ (canonicalFullOperationalLaw V P).real
      {r | r.1 ∈ relErr eps (volSol (atomSet atoms) phi)}) ∧
    ((∫⁻ r, r.2 ∂canonicalFullOperationalLaw V P) ≤
      cvShapeClosedOperationalRuntimeEnvelope atoms phi eps deltaRun
        runtimeConstant radialR) := by
  let deltaRun := 4 * delta / 5
  have hd0 : 0 < deltaRun := by dsimp [deltaRun]; linarith
  have hd1 : deltaRun ≤ 1 := by dsimp [deltaRun]; linarith
  letI : NeZero n := ⟨Nat.ne_of_gt hn⟩
  let V := expectedQueryVolumeAlgorithmOfSourceOneRunCertificates n
    runtimeConstant radialR Omega oneLaw cost value hcert
  letI := V.mΩ
  let P := canonicalCappedPolyHybridPlugin atoms phi eps deltaRun V
    h_eps_pos h_eps_le hn hphi hvol
  have hmain :=
    ttc_volume_estimate_operational_sourceSharp_fullTrajectory_closedRuntime
      atoms phi eps delta runtimeConstant radialR Omega oneLaw cost value hcert
      hconstant h_eps_pos h_eps_le h_delta_pos h_delta_le hn hphi hvol
  refine ⟨hmain.1, hmain.2.trans ?_⟩
  exact explicitClosedOperationalRuntimeEnvelope_le_cvShape atoms phi eps deltaRun
    runtimeConstant radialR hconstant h_eps_pos h_eps_le hd0 hd1 hn hphi hvol

#print axioms sourceCallQueryEnvelope_le_cap
#print axioms sourceCall_radial_sq_le_cap
#print axioms sourceCallQueryEnvelope_le_cvShape
#print axioms sourceCallQueryCap_le_cvShape
#print axioms polyGoodRateCap_le_canonicalRateThreshold
#print axioms polyGoodRateCap_le_canonicalClosedRateThreshold
#print axioms canonicalRateThreshold_le_closed
#print axioms canonicalHybridSamplerQueryBound_le_endpointCap
#print axioms eight_le_canonicalHybridSamplerQueryBound
#print axioms canonicalEndpoint_paperComparison_forces_eight
#print axioms canonicalHybridSamplerQueryBound_ne_top
#print axioms canonicalEndpointInspectionCap_ne_top
#print axioms ttcSourceVolumeQueryEnvelope_le_explicitCap
#print axioms canonicalCappedSampleQueryEnvelope_le_explicitCaps
#print axioms operationalEnvelopes_le_explicitRuntime
#print axioms explicitOperationalRuntimeEnvelope_le_closed
#print axioms explicitClosedOperationalRuntimeEnvelope_le_cvShape
#print axioms ttc_volume_estimate_operational_sourceSharp_fullTrajectory_explicitRuntime
#print axioms ttc_volume_estimate_operational_sourceSharp_fullTrajectory_closedRuntime
#print axioms ttc_volume_estimate_operational_sourceSharp_fullTrajectory_cvShapeRuntime

end Ttc.TTCUnconditionalExplicitRuntime

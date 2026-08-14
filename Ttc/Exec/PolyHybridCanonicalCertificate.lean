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
#print axioms polyHybridKernel_accuracy_canonical

end Ttc.ConcreteHybridCanonicalOwnerPoly

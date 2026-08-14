/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import Ttc.Volume.CVEstimatorNonuniform
import Arlib.Convexity.GaussianCooling.CouplingRoutePacked

/-!
# Product-space plumbing for `k` samples per Cousins--Vempala phase

The elementary coordinate is indexed by `(run, phase, sample)`.  The inner `sample`
coordinates are packed into `Fin k → E`, while the existing `RunSpace` supplies the outer
independence between phases and runs.  These lemmas discharge the independence and marginal
law obligations of the accelerated estimator without treating `k` functions of one draw as
independent.
-/

namespace Ttc.CVPacked

open MeasureTheory ProbabilityTheory

variable {r m k : ℕ} {E : Type*} [MeasurableSpace E]

/-- One elementary score read from its own `(run, phase, sample)` coordinate. -/
noncomputable def sampleScore (g : Fin r → Fin m → Fin k → E → ℝ)
    (j : Fin r) (i : Fin m) (l : Fin k)
    (ω : Arlib.Probability.RunSpace (Fin k → E) r m) : ℝ :=
  g j i l (ω j i l)

/-- The average of the `k` elementary scores at one run and phase. -/
noncomputable def phaseAvg (g : Fin r → Fin m → Fin k → E → ℝ)
    (j : Fin r) (i : Fin m)
    (ω : Arlib.Probability.RunSpace (Fin k → E) r m) : ℝ :=
  CVEst.avgOf k (sampleScore g j i) ω

theorem measurable_sampleScore {g : Fin r → Fin m → Fin k → E → ℝ}
    (hg : ∀ j i l, Measurable (g j i l)) (j : Fin r) (i : Fin m) (l : Fin k) :
    Measurable (sampleScore g j i l) :=
  (hg j i l).comp ((measurable_pi_apply l).comp
    ((measurable_pi_apply i).comp (measurable_pi_apply j)))

theorem measurable_phaseAvg {g : Fin r → Fin m → Fin k → E → ℝ}
    (hg : ∀ j i l, Measurable (g j i l)) (j : Fin r) (i : Fin m) :
    Measurable (phaseAvg g j i) := by
  unfold phaseAvg CVEst.avgOf
  exact (Finset.measurable_fun_sum _ fun l _ => measurable_sampleScore hg j i l).div
    measurable_const

omit [MeasurableSpace E] in
/-- A uniform bound on elementary scores is preserved by their empirical average. -/
theorem abs_phaseAvg_le {g : Fin r → Fin m → Fin k → E → ℝ}
    (hk : 0 < k) {B : ℝ}
    (hgb : ∀ j i l x, |g j i l x| ≤ B) (j : Fin r) (i : Fin m)
    (ω : Arlib.Probability.RunSpace (Fin k → E) r m) :
    |phaseAvg g j i ω| ≤ B := by
  unfold phaseAvg CVEst.avgOf
  rw [abs_div]
  have hkR : (0 : ℝ) < k := by exact_mod_cast hk
  have hsum : |∑ l, sampleScore g j i l ω| ≤ (k : ℝ) * B := by
    calc
      |∑ l, sampleScore g j i l ω| ≤ ∑ l, |sampleScore g j i l ω| :=
        Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _l : Fin k, B := Finset.sum_le_sum fun l _ => hgb j i l _
      _ = (k : ℝ) * B := by simp
  rw [abs_of_pos hkR, div_le_iff₀ hkR]
  simpa [mul_comm] using hsum

/-- The finite product of packed phase averages is in `L²` under the score bound already
needed by the sampler-to-estimator coupling. -/
theorem memLp_prod_phaseAvg
    (ν : Fin r → Fin m → Fin k → Measure E)
    [∀ j i l, IsProbabilityMeasure (ν j i l)]
    {g : Fin r → Fin m → Fin k → E → ℝ}
    (hg : ∀ j i l, Measurable (g j i l)) (hk : 0 < k)
    {B : ℝ} (hgb : ∀ j i l x, |g j i l x| ≤ B) (j : Fin r) :
    MemLp (fun ω => ∏ i, phaseAvg g j i ω) 2
      (Arlib.Probability.runMeasure (Arlib.GaussianCooling.packedPhaseLaw ν)) := by
  have hmeas : Measurable (fun ω => ∏ i, phaseAvg g j i ω) :=
    Finset.measurable_fun_prod _ fun i _ => measurable_phaseAvg hg j i
  refine MemLp.of_bound hmeas.aestronglyMeasurable (B ^ m) ?_
  filter_upwards with ω
  rw [Real.norm_eq_abs, Finset.abs_prod]
  calc
    ∏ i : Fin m, |phaseAvg g j i ω| ≤ ∏ _i : Fin m, B :=
      Finset.prod_le_prod (fun i _ => abs_nonneg _) fun i _ =>
        abs_phaseAvg_le hk hgb j i ω
    _ = B ^ m := by rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]

/-- Projection onto an elementary coordinate preserves its declared marginal law. -/
theorem measurePreserving_sampleCoord
    (ν : Fin r → Fin m → Fin k → Measure E)
    [∀ j i l, IsProbabilityMeasure (ν j i l)] (j : Fin r) (i : Fin m) (l : Fin k) :
    MeasurePreserving
      (fun ω : Arlib.Probability.RunSpace (Fin k → E) r m => ω j i l)
      (Arlib.Probability.runMeasure (Arlib.GaussianCooling.packedPhaseLaw ν))
      (ν j i l) :=
  (measurePreserving_eval (ν j i) l).comp
    (Arlib.Probability.measurePreserving_coord
      (Arlib.GaussianCooling.packedPhaseLaw ν) j i)

/-- Each score has exactly the integral of its elementary marginal. -/
theorem integral_sampleScore
    (ν : Fin r → Fin m → Fin k → Measure E)
    [∀ j i l, IsProbabilityMeasure (ν j i l)]
    {g : Fin r → Fin m → Fin k → E → ℝ}
    (hg : ∀ j i l, Measurable (g j i l)) (j : Fin r) (i : Fin m) (l : Fin k) :
    ∫ ω, sampleScore g j i l ω
        ∂(Arlib.Probability.runMeasure (Arlib.GaussianCooling.packedPhaseLaw ν)) =
      ∫ x, g j i l x ∂(ν j i l) := by
  have hmp := measurePreserving_sampleCoord ν j i l
  rw [← hmp.map_eq, integral_map hmp.measurable.aemeasurable]
  · rfl
  · rw [hmp.map_eq]
    exact (hg j i l).aestronglyMeasurable

/-- `L²` membership transports from an elementary marginal to the full run space. -/
theorem memLp_sampleScore
    (ν : Fin r → Fin m → Fin k → Measure E)
    [∀ j i l, IsProbabilityMeasure (ν j i l)]
    {g : Fin r → Fin m → Fin k → E → ℝ}
    (j : Fin r) (i : Fin m) (l : Fin k) (hL2 : MemLp (g j i l) 2 (ν j i l)) :
    MemLp (sampleScore g j i l) 2
      (Arlib.Probability.runMeasure (Arlib.GaussianCooling.packedPhaseLaw ν)) := by
  change MemLp (fun ω => g j i l (ω j i l)) 2
    (Arlib.Probability.runMeasure (Arlib.GaussianCooling.packedPhaseLaw ν))
  exact hL2.comp_measurePreserving (measurePreserving_sampleCoord ν j i l)

/-- The `k` elementary scores within a phase are genuinely independent. -/
theorem iIndepFun_sampleScore
    (ν : Fin r → Fin m → Fin k → Measure E)
    [∀ j i l, IsProbabilityMeasure (ν j i l)]
    {g : Fin r → Fin m → Fin k → E → ℝ}
    (hg : ∀ j i l, Measurable (g j i l)) (j : Fin r) (i : Fin m) :
    iIndepFun (sampleScore g j i)
      (Arlib.Probability.runMeasure (Arlib.GaussianCooling.packedPhaseLaw ν)) := by
  have hinner : iIndepFun (fun l (η : Fin k → E) => g j i l (η l))
      (Arlib.GaussianCooling.packedPhaseLaw ν j i) :=
    iIndepFun_pi fun l => (hg j i l).aemeasurable
  change iIndepFun (fun l ω => g j i l (ω j i l))
    (Arlib.Probability.runMeasure (Arlib.GaussianCooling.packedPhaseLaw ν))
  exact Arlib.Probability.iIndepFun_comp_measurePreserving
    (T := fun ω : Arlib.Probability.RunSpace (Fin k → E) r m => ω j i)
    (Arlib.Probability.measurePreserving_coord
      (Arlib.GaussianCooling.packedPhaseLaw ν) j i)
    (fun l => (hg j i l).comp (measurable_pi_apply l)) hinner

/-- Hence any two distinct elementary samples within one phase are independent. -/
theorem pairwise_indepFun_sampleScore
    (ν : Fin r → Fin m → Fin k → Measure E)
    [∀ j i l, IsProbabilityMeasure (ν j i l)]
    {g : Fin r → Fin m → Fin k → E → ℝ}
    (hg : ∀ j i l, Measurable (g j i l)) (j : Fin r) (i : Fin m) :
    Pairwise fun l l' => IndepFun (sampleScore g j i l) (sampleScore g j i l')
      (Arlib.Probability.runMeasure (Arlib.GaussianCooling.packedPhaseLaw ν)) :=
  fun _ _ hne => (iIndepFun_sampleScore ν hg j i).indepFun hne

/-- The whole `Fin k → ℝ` score vectors are independent across phases.  This is the
second half of `CVEst.CoordinateIndep`; it comes from the outer product in `RunSpace`,
not from reusing the scalar-coordinate independence within a phase. -/
theorem iIndepFun_phaseVector_sampleScore
    (ν : Fin r → Fin m → Fin k → Measure E)
    [∀ j i l, IsProbabilityMeasure (ν j i l)]
    {g : Fin r → Fin m → Fin k → E → ℝ}
    (hg : ∀ j i l, Measurable (g j i l)) (j : Fin r) :
    iIndepFun
      (CVEst.phaseVector (fun i l => sampleScore g j i l))
      (Arlib.Probability.runMeasure (Arlib.GaussianCooling.packedPhaseLaw ν)) := by
  let fp : Fin m → (Fin k → E) → (Fin k → ℝ) := fun i η l => g j i l (η l)
  have hfp : ∀ i, Measurable (fp i) := by
    intro i
    exact measurable_pi_lambda _ fun l => (hg j i l).comp (measurable_pi_apply l)
  have hinner : iIndepFun (fun i (η : Fin m → Fin k → E) => fp i (η i))
      (Measure.pi fun i => Arlib.GaussianCooling.packedPhaseLaw ν j i) :=
    iIndepFun_pi fun i => (hfp i).aemeasurable
  have houter := Arlib.Probability.iIndepFun_comp_measurePreserving
    (T := fun ω : Arlib.Probability.RunSpace (Fin k → E) r m => ω j)
    (measurePreserving_eval
      (fun j => Measure.pi fun i => Arlib.GaussianCooling.packedPhaseLaw ν j i) j)
    (fun i => (hfp i).comp (measurable_pi_apply i)) hinner
  have heq : CVEst.phaseVector (fun i l => sampleScore g j i l) =
      fun i ω => fp i ((ω j) i) := by
    funext i ω l
    rfl
  rw [heq]
  simpa only [Arlib.Probability.runMeasure, Function.comp_apply] using houter

/-- The packed product space satisfies the exact two-level independence contract used by
the nonuniform accelerated estimator. -/
theorem coordinateIndep_sampleScore
    (ν : Fin r → Fin m → Fin k → Measure E)
    [∀ j i l, IsProbabilityMeasure (ν j i l)]
    {g : Fin r → Fin m → Fin k → E → ℝ}
    (hg : ∀ j i l, Measurable (g j i l)) (j : Fin r) :
    CVEst.CoordinateIndep (fun i l => sampleScore g j i l)
      (Arlib.Probability.runMeasure (Arlib.GaussianCooling.packedPhaseLaw ν)) :=
  ⟨fun i => iIndepFun_sampleScore ν hg j i,
    iIndepFun_phaseVector_sampleScore ν hg j⟩

/-- Phase averages within a fixed run are independent. -/
theorem iIndepFun_phaseAvg
    (ν : Fin r → Fin m → Fin k → Measure E)
    [∀ j i l, IsProbabilityMeasure (ν j i l)]
    {g : Fin r → Fin m → Fin k → E → ℝ}
    (hg : ∀ j i l, Measurable (g j i l)) (j : Fin r) :
    iIndepFun (phaseAvg g j)
      (Arlib.Probability.runMeasure (Arlib.GaussianCooling.packedPhaseLaw ν)) := by
  let fp : Fin m → (Fin k → E) → ℝ := fun i η =>
    CVEst.avgOf k (fun l η' => g j i l (η' l)) η
  have hfp : ∀ i, Measurable (fp i) := by
    intro i
    unfold fp CVEst.avgOf
    exact (Finset.measurable_fun_sum _ fun l _ =>
      (hg j i l).comp (measurable_pi_apply l)).div
      measurable_const
  have hinner : iIndepFun (fun i (η : Fin m → Fin k → E) => fp i (η i))
      (Measure.pi fun i => Arlib.GaussianCooling.packedPhaseLaw ν j i) :=
    iIndepFun_pi fun i => (hfp i).aemeasurable
  have houter := Arlib.Probability.iIndepFun_comp_measurePreserving
    (T := fun ω : Arlib.Probability.RunSpace (Fin k → E) r m => ω j)
    (measurePreserving_eval
      (fun j => Measure.pi fun i => Arlib.GaussianCooling.packedPhaseLaw ν j i) j)
    (fun i => (hfp i).comp (measurable_pi_apply i)) hinner
  have heq : (phaseAvg g j) = fun i ω => fp i ((ω j) i) := by
    funext i ω
    rfl
  rw [heq]
  simpa only [Arlib.Probability.runMeasure, Function.comp_apply] using houter

end Ttc.CVPacked

#print axioms Ttc.CVPacked.measurePreserving_sampleCoord
#print axioms Ttc.CVPacked.integral_sampleScore
#print axioms Ttc.CVPacked.memLp_sampleScore
#print axioms Ttc.CVPacked.abs_phaseAvg_le
#print axioms Ttc.CVPacked.memLp_prod_phaseAvg
#print axioms Ttc.CVPacked.pairwise_indepFun_sampleScore
#print axioms Ttc.CVPacked.iIndepFun_phaseVector_sampleScore
#print axioms Ttc.CVPacked.coordinateIndep_sampleScore
#print axioms Ttc.CVPacked.iIndepFun_phaseAvg

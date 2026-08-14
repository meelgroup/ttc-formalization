/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import Ttc.Volume.CVSampler
import Arlib.Convexity.GaussianCooling.PhaseFromTVGeneral

/-!
# A general-rate speedy sampler volume constructor

The direct general-rate constructor `cousinsVempalaOfSamplerCooling` quantifies its sampler
guarantee over every natural index.  That does not match the speedy Gaussian sampler, whose
identification with `coolLaw` is valid at the actual Gaussian phases `i : Fin phases`.

This file instead generalises the amended, `Fin phases` constructor.  Its variance proof is
`hphase_var_of_tvLe_of_flat_general`, so the fixed-rate condition
`2 * phases <= n * varBudget` is replaced by the genuine general-rate condition

`(1 - alpha^2)^(-(n+1)) <= 1 + varBudget / phases`.

The second constructor then supplies the total-variation hypothesis with the speedy sampler
from `CVSampler`.  No terminal/uniform index is silently assigned a vacuous error.
-/

namespace Ttc

open MeasureTheory Metric Set
open scoped ENNReal

variable {n : ℕ}

/-- The `Fin phases` amended estimator at an arbitrary cooling rate `alpha`.

This is the general-rate counterpart of
`VolumeAlgorithm.cousinsVempalaOfRunsApproxMeanAmended`.  The mean argument is unchanged;
the variance argument is discharged by `hphase_var_of_tvLe_of_flat_general`. -/
noncomputable def VolumeAlgorithm.cousinsVempalaOfRunsApproxMeanAmendedGeneral
    (n : ℕ) (E : Type) [MeasurableSpace E] (nu : ℕ → ℕ → Measure E)
    [∀ j i, IsProbabilityMeasure (nu j i)]
    (hn : 3 ≤ n)
    (phases : Set (Space n) → ℝ → ℝ → ℕ)
    (sigmaSq : Set (Space n) → ℝ → ℝ → ℕ → ℝ)
    (Rad alpha : Set (Space n) → ℝ → ℝ → ℝ)
    (X : Set (Space n) → ℝ → ℝ → ℕ → ℕ → E → Space n)
    (tvErr : Set (Space n) → ℝ → ℝ → ℕ → ℕ → ℝ≥0∞)
    (B : ℝ)
    (hsigma : ∀ K eps p j, 0 < sigmaSq K eps p j)
    (hX : ∀ K eps p j i, Measurable (X K eps p j i))
    (hgb : ∀ K eps p j i x,
      |Arlib.GaussianCooling.phaseScore (phases K eps p) (sigmaSq K eps p)
        (interior K) i (X K eps p j i x)| ≤ B)
    (halpha0 : ∀ K eps p, 0 ≤ alpha K eps p)
    (halpha1 : ∀ K eps p, alpha K eps p < 1)
    (hKrad : ∀ (K : Set (Space n)) (eps p : ℝ), 0 < eps → 0 < p → p < 1 →
      Convex ℝ K → ball (0 : Space n) 1 ⊆ K → volume K ≠ ⊤ →
      ∀ (_j : ℕ) (_i : Fin (phases K eps p)),
      K ⊆ closedBall (0 : Space n) (Rad K eps p))
    (htop : ∀ (K : Set (Space n)) (eps p : ℝ), 0 < eps → 0 < p → p < 1 →
      Convex ℝ K → ball (0 : Space n) 1 ⊆ K → volume K ≠ ⊤ →
      ∀ (j : ℕ) (i : Fin (phases K eps p)), tvErr K eps p j (i : ℕ) ≠ ⊤)
    (hTV : ∀ (K : Set (Space n)) (eps p : ℝ), 0 < eps → 0 < p → p < 1 →
      Convex ℝ K → ball (0 : Space n) 1 ⊆ K → volume K ≠ ⊤ →
      ∀ (j : ℕ) (i : Fin (phases K eps p)),
      Arlib.TVLe ((nu j (i : ℕ)).map (X K eps p j (i : ℕ)))
        (Arlib.GaussianCooling.coolLaw (phases K eps p) (sigmaSq K eps p) K (i : ℕ))
        (tvErr K eps p j (i : ℕ)))
    (hslackMean : ∀ (K : Set (Space n)) (eps p : ℝ), 0 < eps → 0 < p → p < 1 →
      Convex ℝ K → ball (0 : Space n) 1 ⊆ K → volume K ≠ ⊤ →
      ∀ (j : ℕ) (i : Fin (phases K eps p)),
      Real.exp (Rad K eps p ^ 2 / (2 * sigmaSq K eps p (i : ℕ)))
          * (tvErr K eps p j (i : ℕ)).toReal
        ≤ eps / (2 * (2 + eps) * (phases K eps p : ℝ))
            * (Arlib.GaussianCooling.chain (phases K eps p) (sigmaSq K eps p) K
                ((i : ℕ) + 1) /
              Arlib.GaussianCooling.chain (phases K eps p) (sigmaSq K eps p) K (i : ℕ)))
    (hrate : ∀ (K : Set (Space n)) (eps p : ℝ), 0 < eps → 0 < p → p < 1 →
      Convex ℝ K → ball (0 : Space n) 1 ⊆ K → volume K ≠ ⊤ →
      ∀ (_j : ℕ) (i : Fin (phases K eps p)),
      sigmaSq K eps p ((i : ℕ) + 1) =
        sigmaSq K eps p (i : ℕ) * (1 + alpha K eps p))
    (hbudget : ∀ (K : Set (Space n)) (eps p : ℝ), 0 < eps → 0 < p → p < 1 →
      Convex ℝ K → ball (0 : Space n) 1 ⊆ K → volume K ≠ ⊤ →
      ∀ (_j : ℕ) (_i : Fin (phases K eps p)),
      ((1 : ℝ) - alpha K eps p ^ 2)⁻¹ ^ (n + 1)
        ≤ 1 + Arlib.GaussianCooling.varBudget (eps / 2) / (phases K eps p : ℝ))
    (hflat : ∀ (K : Set (Space n)) (eps p : ℝ), 0 < eps → 0 < p → p < 1 →
      Convex ℝ K → ball (0 : Space n) 1 ⊆ K → volume K ≠ ⊤ →
      ∀ (_j : ℕ) (i : Fin (phases K eps p)), (i : ℕ) + 1 = phases K eps p →
      Rad K eps p ^ 2 ≤ 2 * sigmaSq K eps p (i : ℕ)
        * Real.log (((1 : ℝ) - alpha K eps p ^ 2)⁻¹ ^ (n + 1)))
    (hslackVar : ∀ (K : Set (Space n)) (eps p : ℝ), 0 < eps → 0 < p → p < 1 →
      Convex ℝ K → ball (0 : Space n) 1 ⊆ K → volume K ≠ ⊤ →
      ∀ (j : ℕ) (i : Fin (phases K eps p)),
      (tvErr K eps p j (i : ℕ)).toReal
          * (Real.exp (Rad K eps p ^ 2 / (2 * sigmaSq K eps p (i : ℕ))) ^ 2
              * (1 + 2 * (1 + Arlib.GaussianCooling.varBudget (eps / 2)
                  / (phases K eps p : ℝ))))
        ≤ (1 + Arlib.GaussianCooling.varBudget (eps / 2) / (phases K eps p : ℝ)
              - ((1 : ℝ) - alpha K eps p ^ 2)⁻¹ ^ (n + 1))
            * (Arlib.GaussianCooling.chain (phases K eps p) (sigmaSq K eps p) K
                ((i : ℕ) + 1) /
              Arlib.GaussianCooling.chain (phases K eps p) (sigmaSq K eps p) K (i : ℕ)) ^ 2) :
    VolumeAlgorithm n :=
  VolumeAlgorithm.cousinsVempalaOfRunsApproxMean n E nu phases sigmaSq
    (fun K eps p j i x =>
      Arlib.GaussianCooling.phaseScore (phases K eps p) (sigmaSq K eps p)
        (interior K) i (X K eps p j i x))
    B hsigma
    (fun K eps p j i =>
      (Arlib.GaussianCooling.measurable_phaseScore isOpen_interior.measurableSet i).comp
        (hX K eps p j i))
    hgb
    (fun K eps p heps hp hp1 hconv hball hfin j i =>
      Arlib.GaussianCooling.hphase_mean_of_tvLe E phases sigmaSq nu X Rad tvErr hsigma hX
        hKrad htop hTV hslackMean K eps p heps hp hp1 hconv hball hfin j i)
    (fun K eps p heps hp hp1 hconv hball hfin j i =>
      Arlib.GaussianCooling.hphase_var_of_tvLe_of_flat_general E hn phases sigmaSq nu X Rad
        alpha tvErr hsigma hX halpha0 halpha1 hKrad htop hTV hrate hbudget hflat hslackVar
        K eps p heps hp hp1 hconv hball hfin j i)

/-- A general-rate volume estimator whose per-phase TV hypothesis is discharged by the
lazy speedy Metropolis--Gaussian sampler.

Unlike the fixed-rate adapter, this accepts any `alpha` satisfying the general-rate moment
budget.  The additional `alpha <= 2/n` condition is exactly the overlap window needed by
the existing warm-start theorem. -/
noncomputable def VolumeAlgorithm.cousinsVempalaOfSpeedySamplerGeneral
    (n : ℕ) (hn : 21 ≤ n)
    (phases : Set (Space n) → ℝ → ℝ → ℕ)
    (sigmaSq : Set (Space n) → ℝ → ℝ → ℕ → ℝ)
    (Rad alpha : Set (Space n) → ℝ → ℝ → ℝ)
    (stepSize : Set (Space n) → ℝ → ℝ → ℝ)
    (start : Set (Space n) → ℝ → ℝ → Measure (Space n))
    (steps : Set (Space n) → ℝ → ℝ → ℕ → ℕ)
    (acc warmM : Set (Space n) → ℝ → ℝ → ℝ) (B : ℝ)
    (hsigma : ∀ K eps p j, 0 < sigmaSq K eps p j)
    (hstart : ∀ K eps p, IsProbabilityMeasure (start K eps p))
    (hgb : ∀ K eps p (j i : ℕ) x,
      |Arlib.GaussianCooling.phaseScore (phases K eps p) (sigmaSq K eps p)
        (interior K) i (Ttc.CVSampler.coinX (K, eps, p) x)| ≤ B)
    (halpha0 : ∀ K eps p, 0 ≤ alpha K eps p)
    (halpha1 : ∀ K eps p, alpha K eps p < 1)
    (halpha2n : ∀ K eps p, alpha K eps p ≤ 2 / (n : ℝ))
    (hKrad : ∀ (K : Set (Space n)) (eps p : ℝ), 0 < eps → 0 < p → p < 1 →
      Convex ℝ K → ball (0 : Space n) 1 ⊆ K → volume K ≠ ⊤ →
      ∀ x ∈ K, ‖x‖ ≤ Rad K eps p)
    (hslackMean : ∀ (K : Set (Space n)) (eps p : ℝ), 0 < eps → 0 < p → p < 1 →
      Convex ℝ K → ball (0 : Space n) 1 ⊆ K → volume K ≠ ⊤ →
      ∀ (j : ℕ) (i : Fin (phases K eps p)),
      Real.exp (Rad K eps p ^ 2 / (2 * sigmaSq K eps p (i : ℕ)))
          * (64 * ENNReal.ofReal (acc K eps p)).toReal
        ≤ eps / (2 * (2 + eps) * (phases K eps p : ℝ))
            * (Arlib.GaussianCooling.chain (phases K eps p) (sigmaSq K eps p) K
                ((i : ℕ) + 1) /
              Arlib.GaussianCooling.chain (phases K eps p) (sigmaSq K eps p) K (i : ℕ)))
    (hbudget : ∀ (K : Set (Space n)) (eps p : ℝ), 0 < eps → 0 < p → p < 1 →
      Convex ℝ K → ball (0 : Space n) 1 ⊆ K → volume K ≠ ⊤ →
      ∀ (_j : ℕ) (_i : Fin (phases K eps p)),
      ((1 : ℝ) - alpha K eps p ^ 2)⁻¹ ^ (n + 1)
        ≤ 1 + Arlib.GaussianCooling.varBudget (eps / 2) / (phases K eps p : ℝ))
    (hflat : ∀ (K : Set (Space n)) (eps p : ℝ), 0 < eps → 0 < p → p < 1 →
      Convex ℝ K → ball (0 : Space n) 1 ⊆ K → volume K ≠ ⊤ →
      ∀ (_j : ℕ) (i : Fin (phases K eps p)), (i : ℕ) + 1 = phases K eps p →
      Rad K eps p ^ 2 ≤ 2 * sigmaSq K eps p (i : ℕ)
        * Real.log (((1 : ℝ) - alpha K eps p ^ 2)⁻¹ ^ (n + 1)))
    (hslackVar : ∀ (K : Set (Space n)) (eps p : ℝ), 0 < eps → 0 < p → p < 1 →
      Convex ℝ K → ball (0 : Space n) 1 ⊆ K → volume K ≠ ⊤ →
      ∀ (j : ℕ) (i : Fin (phases K eps p)),
      (64 * ENNReal.ofReal (acc K eps p)).toReal
          * (Real.exp (Rad K eps p ^ 2 / (2 * sigmaSq K eps p (i : ℕ))) ^ 2
              * (1 + 2 * (1 + Arlib.GaussianCooling.varBudget (eps / 2)
                  / (phases K eps p : ℝ))))
        ≤ (1 + Arlib.GaussianCooling.varBudget (eps / 2) / (phases K eps p : ℝ)
              - ((1 : ℝ) - alpha K eps p ^ 2)⁻¹ ^ (n + 1))
            * (Arlib.GaussianCooling.chain (phases K eps p) (sigmaSq K eps p) K
                ((i : ℕ) + 1) /
              Arlib.GaussianCooling.chain (phases K eps p) (sigmaSq K eps p) K (i : ℕ)) ^ 2)
    (hdelta0 : ∀ K eps p, 0 < stepSize K eps p)
    (hdeltan : ∀ K eps p, stepSize K eps p ≤ 1 / (2 * (n : ℝ)))
    (hdeltasigma : ∀ K eps p j,
      stepSize K eps p ≤ Real.sqrt (sigmaSq K eps p j) / (8 * Real.sqrt n))
    (hRad0 : ∀ K eps p, 0 ≤ Rad K eps p)
    (hRadsigma : ∀ K eps p j,
      Rad K eps p ≤ 2 * Real.sqrt (sigmaSq K eps p j) * Real.sqrt n)
    (hrateAll : ∀ K eps p j,
      sigmaSq K eps p (j + 1) = sigmaSq K eps p j * (1 + alpha K eps p))
    (hM : ∀ K eps p, 2 * Real.exp 1 ≤ warmM K eps p)
    (hwarm : ∀ (K : Set (Space n)) (eps p : ℝ), 0 < eps → 0 < p → p < 1 →
      Convex ℝ K → ball (0 : Space n) 1 ⊆ K → volume K ≠ ⊤ →
      Arlib.IsWarm (ENNReal.ofReal (warmM K eps p)) (start K eps p)
        (Arlib.MarkovChains.ellGaussianProb (interior K) (stepSize K eps p)
          (sigmaSq K eps p 0)))
    (hacc0 : ∀ K eps p, 0 < acc K eps p)
    (hacc32 : ∀ K eps p, acc K eps p ≤ 1 / 32)
    (hsteps : ∀ K eps p i,
      4 * 640 ^ 2 * sigmaSq K eps p i * (n : ℝ)
        * (Real.log (warmM K eps p) + 2 * Real.log (1 / acc K eps p))
        / (stepSize K eps p * Real.log 2) ^ 2 + 1 ≤ (steps K eps p i : ℝ)) :
    VolumeAlgorithm n :=
  VolumeAlgorithm.cousinsVempalaOfRunsApproxMeanAmendedGeneral n (Ttc.CVSampler.CoinSpace n)
    (fun _j i => Ttc.CVSampler.coinMeasure
      (Ttc.CVSampler.cvLaw phases sigmaSq stepSize start steps) i)
    (by omega) phases sigmaSq Rad alpha
    (fun K eps p _j _i => Ttc.CVSampler.coinX (K, eps, p))
    (fun K eps p _j _i => 64 * ENNReal.ofReal (acc K eps p)) B hsigma
    (fun _ _ _ _ _ => Ttc.CVSampler.measurable_coinX _) hgb halpha0 halpha1
    (fun K eps p heps hp hp1 hconv hball hfin _j _i x hx =>
      mem_closedBall_zero_iff.mpr (hKrad K eps p heps hp hp1 hconv hball hfin x hx))
    (fun _ _ _ _ _ _ _ _ _ _ _ =>
      ENNReal.mul_ne_top (by simp) ENNReal.ofReal_ne_top)
    (Ttc.CVSampler.hTV_cvLaw hn phases sigmaSq stepSize start steps Rad acc warmM
      (fun K eps p => 1 + alpha K eps p) hsigma hstart hdelta0 hdeltan hdeltasigma hRad0
      hRadsigma (fun K eps p => by linarith [halpha0 K eps p])
      (fun K eps p => by linarith [halpha2n K eps p])
      (fun K eps p j => by rw [hrateAll K eps p j]; ring)
      hM hacc0 hacc32 hsteps
      hKrad
      hwarm)
    hslackMean
    (fun K eps p heps hp hp1 hconv hball hfin j i =>
      hrateAll K eps p (i : ℕ))
    hbudget hflat hslackVar

end Ttc

#print axioms Ttc.VolumeAlgorithm.cousinsVempalaOfRunsApproxMeanAmendedGeneral
#print axioms Ttc.VolumeAlgorithm.cousinsVempalaOfSpeedySamplerGeneral

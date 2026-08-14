/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import Arlib.MarkovChains.Continuous.MetropolisMixingUncond
import Arlib.Convexity.GaussianCooling.WarmChain
import Ttc.Volume.CVSequentialPhaseSampler

/-!
# The direct ordinary-Metropolis phase kernel, and the remaining polynomial blocker

The lazy ordinary Gaussian Metropolis chain is already an honest Markov kernel whose
stationary measure is the Gaussian cooling law.  Consequently a deterministic number of
its steps needs neither the globally normalised rejection in `Ttc.CVSampler.phaseLaw` nor a
fresh-regeneration resource.  This file exposes that operational seam:

* `lazyMetropolisGaussianPhaseKernel` is the `t`-step transition kernel;
* sampling from it is definitionally the `iterate` used by the mixing API;
* it preserves every warmness bound with respect to its Gaussian stationary law;
* along the cooling schedule, the only extra warmness cost is the already proved
  phase-to-phase factor `e`.

This does **not** produce a polynomial sampler on the full class of CV bodies.  The only
polynomial-looking deterministic-time ordinary-chain theorem currently available,
`mixesWithin_lazy_metropolisGaussian_at_operative_step_of_convex`, requires a pointwise local
conductance floor `hell` and a constant acceptance floor `hfloor`.  The final theorem below
packages the machine-checked obstruction from `EllFloor.lean`: on the cube `[-1,1]^n`, for
`n >= 3`, no `theta` can satisfy those two hypotheses.  Thus the shortest missing theorem is
an exceptional-set / `s`-conductance mixing theorem for the Gaussian Metropolis chain (the
Gaussian analogue of `BallWalkTransfer.lean`), not another kernel adapter.  The alternative
speedy time-change route instead needs a strong-Markov identification of successive marked
sojourns and a high-probability deterministic-time bound.
-/

namespace Ttc.CVDirectMetropolisPhase

open MeasureTheory ProbabilityTheory Metric Set
open Arlib Arlib.GaussianCooling
open scoped ENNReal

/-- The honest `t`-step lazy ordinary Gaussian Metropolis transition kernel. -/
noncomputable def lazyMetropolisGaussianPhaseKernel {n : Nat}
    (K : Set (EuclideanSpace Real (Fin n))) (delta sigmaSq : Real) (t : Nat) :
    Kernel (EuclideanSpace Real (Fin n)) (EuclideanSpace Real (Fin n)) :=
  CVSequentialPhaseSampler.iteratedKernel
    (Arlib.MarkovChains.lazy
      (Arlib.MarkovChains.metropolisGaussian K delta sigmaSq)) t

instance lazyMetropolisGaussianPhaseKernel.isMarkovKernel {n : Nat}
    (K : Set (EuclideanSpace Real (Fin n))) (delta sigmaSq : Real) (t : Nat) :
    IsMarkovKernel (lazyMetropolisGaussianPhaseKernel K delta sigmaSq t) := by
  unfold lazyMetropolisGaussianPhaseKernel
  infer_instance

/-- Sampling from the direct phase kernel is exactly deterministic-time iteration of the
ordinary lazy Metropolis chain.  In particular, `t` is already the number of proposal
transitions; there is no random outer rejection count to translate. -/
theorem sampleFrom_lazyMetropolisGaussianPhaseKernel_eq_iterate {n : Nat}
    (K : Set (EuclideanSpace Real (Fin n))) (delta sigmaSq : Real)
    (rho : Measure (EuclideanSpace Real (Fin n))) (t : Nat) :
    CVSequentialPhaseSampler.sampleFromKernel
        (lazyMetropolisGaussianPhaseKernel K delta sigmaSq t) rho =
      Arlib.MarkovChains.iterate
        (Arlib.MarkovChains.lazy
          (Arlib.MarkovChains.metropolisGaussian K delta sigmaSq)) rho t := by
  symm
  exact CVSequentialPhaseSampler.iterate_eq_sampleFrom_iteratedKernel _ _ _

/-- A `MixesWithin` result for the ordinary chain is immediately a sampler-TV result for the
honest direct phase kernel. -/
theorem tvLe_sampleFrom_lazyMetropolisGaussianPhaseKernel_of_mixesWithin {n : Nat}
    {K : Set (EuclideanSpace Real (Fin n))} {delta sigmaSq : Real}
    {rho target : Measure (EuclideanSpace Real (Fin n))} {t : Nat} {eps : ENNReal}
    (hmix : Arlib.MarkovChains.MixesWithin
      (Arlib.MarkovChains.lazy
        (Arlib.MarkovChains.metropolisGaussian K delta sigmaSq))
      target rho t eps) :
    TVLe
      (CVSequentialPhaseSampler.sampleFromKernel
        (lazyMetropolisGaussianPhaseKernel K delta sigmaSq t) rho)
      target eps := by
  rw [sampleFrom_lazyMetropolisGaussianPhaseKernel_eq_iterate]
  exact hmix

/-- The direct phase kernel has the exact conditional-history restart property required by
the LV2 dependence argument.  Thus, once a distributional warm-start mixing theorem is
available, `NuIndep` follows with no `FreshRegenerationResource`: it is ordinary Markov
factorisation of the actual sequential chain. -/
theorem nuIndep_compProd_lazyMetropolisGaussianPhase_of_distributionalWarm
    {H : Type*} [MeasurableSpace H] {n : Nat}
    {rho : Measure H} [IsProbabilityMeasure rho]
    {pi tau : Measure (EuclideanSpace Real (Fin n))} [IsProbabilityMeasure tau]
    {last : H -> EuclideanSpace Real (Fin n)} (hlast : Measurable last)
    {K : Set (EuclideanSpace Real (Fin n))} {delta sigmaSq : Real} {t : Nat}
    {M eps : ENNReal} (hwarm : IsWarm M (rho.map last) pi) (heps : eps ≠ ⊤)
    (hmix : forall eta : Measure (EuclideanSpace Real (Fin n)),
      IsWarm (2 * M) eta pi -> IsProbabilityMeasure eta ->
      TVLe
        (CVSequentialPhaseSampler.sampleFromKernel
          (lazyMetropolisGaussianPhaseKernel K delta sigmaSq t) eta)
        tau eps) :
    NuIndep
      (rho ⊗ₘ Kernel.comap
        (lazyMetropolisGaussianPhaseKernel K delta sigmaSq t) last hlast)
      Prod.fst Prod.snd (2 * eps.toReal) := by
  exact CVSequentialPhaseSampler.nuIndep_compProd_comap_of_distributionalWarm
    (lazyMetropolisGaussianPhaseKernel K delta sigmaSq t) hlast hwarm heps hmix

/-- Iterating the direct lazy phase does not increase its warmness constant. -/
theorem isWarm_sampleFrom_lazyMetropolisGaussianPhaseKernel {n : Nat}
    {K : Set (EuclideanSpace Real (Fin n))} (hK : MeasurableSet K)
    (delta sigmaSq : Real) {rho : Measure (EuclideanSpace Real (Fin n))}
    {M : ENNReal} (hwarm : IsWarm M rho
      (Arlib.uniformOn
        ((volume : Measure (EuclideanSpace Real (Fin n))).withDensity
          (Arlib.MarkovChains.gaussianWeight sigmaSq)) K))
    (t : Nat) :
    IsWarm M
      (CVSequentialPhaseSampler.sampleFromKernel
        (lazyMetropolisGaussianPhaseKernel K delta sigmaSq t) rho)
      (Arlib.uniformOn
        ((volume : Measure (EuclideanSpace Real (Fin n))).withDensity
          (Arlib.MarkovChains.gaussianWeight sigmaSq)) K) := by
  rw [sampleFrom_lazyMetropolisGaussianPhaseKernel_eq_iterate]
  exact Arlib.MarkovChains.isWarm_iterate_of_invariant hwarm
    ((Arlib.MarkovChains.isReversible_lazy
      (Arlib.MarkovChains.isReversible_metropolisGaussian hK delta sigmaSq)).invariant) t

/-- Sequential use of the direct kernel needs no rejection restart.  If the incoming law is
`M`-warm for phase `i`, its output remains `M`-warm for phase `i`, hence is `M*e`-warm for
phase `i+1`.  This is enough for polynomial mixing because the direct-chain deadline uses
`log M`; unlike the wasted-step bound, it never multiplies the operational cost by `M`.

The factor still accumulates if approximate outputs are passed through many phases.  No
general theorem in the repository resets an approximate law to constant `L-infinity`
warmness, and total variation alone cannot do so. -/
theorem isWarm_directPhaseOutput_nextCoolLaw {n m : Nat}
    {sigmaSq : Nat -> Real} (hsigma : forall j, 0 < sigmaSq j)
    {K : Set (EuclideanSpace Real (Fin n))} (hK : MeasurableSet K)
    (hKc : Convex Real K) (hball : ball (0 : EuclideanSpace Real (Fin n)) 1 ⊆ K)
    (hfin : volume K ≠ ⊤) {i : Nat} (hi : i + 1 < m)
    {cc : Real} (hcc1 : 1 <= cc) (hcc : cc <= 1 + 2 / (n : Real))
    (hsched : sigmaSq (i + 1) = cc * sigmaSq i)
    {rho : Measure (EuclideanSpace Real (Fin n))} {M : ENNReal}
    (hwarm : IsWarm M rho (coolLaw m sigmaSq K i)) (delta : Real) (t : Nat) :
    IsWarm (M * ENNReal.ofReal (Real.exp 1))
      (CVSequentialPhaseSampler.sampleFromKernel
        (lazyMetropolisGaussianPhaseKernel K delta (sigmaSq i) t) rho)
      (coolLaw m sigmaSq K (i + 1)) := by
  have hpres : IsWarm M
      (CVSequentialPhaseSampler.sampleFromKernel
        (lazyMetropolisGaussianPhaseKernel K delta (sigmaSq i) t) rho)
      (coolLaw m sigmaSq K i) := by
    rw [coolLaw_eq_uniformOn_gaussianWeight hsigma hK hball hfin
      (Nat.lt_of_succ_lt hi)] at hwarm ⊢
    exact isWarm_sampleFrom_lazyMetropolisGaussianPhaseKernel hK delta (sigmaSq i) hwarm t
  exact hpres.trans
    (isWarm_coolLaw_succ_exp hi hK hfin hKc hball hsigma hcc1 hcc hsched)

/-- The hypotheses used by the current polynomial-looking ordinary-Metropolis conductance
route cannot hold on the cube.  This is the exact interface blocker for promoting the direct
kernel above to a general CV phase sampler. -/
theorem not_exists_localFloor_bundle_on_cube {n : Nat} (hn : 3 <= n)
    {sigma delta R : Real} (hsigma : 0 < sigma) (hdelta : 0 <= delta) (hR : 0 <= R) :
    ¬ (exists theta : Real,
      (forall x, x ∈ {y : EuclideanSpace Real (Fin n) | forall j, abs (y j) <= 1} ->
        ENNReal.ofReal theta <=
          Arlib.MarkovChains.ell
            {y : EuclideanSpace Real (Fin n) | forall j, abs (y j) <= 1} delta x) /\
      1 <= 20 * Real.exp (-(2 * R * delta + delta ^ 2) / (2 * sigma ^ 2)) *
        (1 / 4) * theta) := by
  rintro ⟨theta, hell, hfloor⟩
  exact Arlib.MarkovChains.metropolis_ell_floor_unsatisfiable_on_cube
    hn hsigma hdelta hR hell hfloor

end Ttc.CVDirectMetropolisPhase

#print axioms Ttc.CVDirectMetropolisPhase.sampleFrom_lazyMetropolisGaussianPhaseKernel_eq_iterate
#print axioms Ttc.CVDirectMetropolisPhase.tvLe_sampleFrom_lazyMetropolisGaussianPhaseKernel_of_mixesWithin
#print axioms Ttc.CVDirectMetropolisPhase.nuIndep_compProd_lazyMetropolisGaussianPhase_of_distributionalWarm
#print axioms Ttc.CVDirectMetropolisPhase.isWarm_sampleFrom_lazyMetropolisGaussianPhaseKernel
#print axioms Ttc.CVDirectMetropolisPhase.isWarm_directPhaseOutput_nextCoolLaw
#print axioms Ttc.CVDirectMetropolisPhase.not_exists_localFloor_bundle_on_cube

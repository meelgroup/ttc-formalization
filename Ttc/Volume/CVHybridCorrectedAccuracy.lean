/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import Ttc.Volume.CVFreshRestartDependence
import Ttc.Volume.CVHybridPhaseScoreVariance

/-!
# Corrected dependent accuracy on the source hybrid schedule

This file packages the operational dependence assumptions for all hybrid phases into one
`HybridFreshOperational` value.  Its essential field is a phasewise
`FreshRegenerationResource`; the remaining fields state positive rejection mass, target
TV, and the identification of history/point statistics with the corrected `U,V`
recursion.  No statewise regeneration is inferred.

The capstone combines that package with the hybrid per-phase variance factors, their
cold/hot product budget, and `corrected_lem_accuracy_concrete`.
-/

namespace Ttc.CVHybridCorrected

open MeasureTheory ProbabilityTheory Metric Set
open Arlib Arlib.Probability Arlib.GaussianCooling
open Arlib.GaussianCooling.Chunked
open Ttc.CVFreshRestartKernel Ttc.CVFreshRestartDependence
open Ttc.CVCorrected Ttc.CVHybridSchedule
open scoped ENNReal BigOperators Pointwise

variable {n : Nat}

/-- Every active hybrid averaged phase factor is bounded by the conservative factor used
by the corrected scalar bundle. -/
theorem phaseVarFactor_le_one_add_eight_div {J i : Nat} (hn : 1 ≤ n)
    {k N s0 : Real} (hk : 0 < k) (hN : 0 < N) (hs0 : 0 < s0)
    (hbelow : ∀ j < J, adaptiveChunkStart N (coldEnd n s0) j ≤ N)
    (hi : i < coldPhases n s0 + adaptiveChunkOffset N (coldEnd n s0) J) :
    phaseVarFactor n k N s0 i ≤ 1 + 8 / k := by
  have hnR : (1 : Real) ≤ n := by exact_mod_cast hn
  have hn0 : (0 : Real) < n := by positivity
  by_cases hicold : i < coldPhases n s0
  · rw [phaseVarFactor, if_pos hicold]
    have hden : 0 < k * (n : Real) := mul_pos hk hn0
    rw [add_le_add_iff_left]
    rw [div_le_div_iff₀ hden hk]
    nlinarith
  · let t := i - coldPhases n s0
    have ht : t < adaptiveChunkOffset N (coldEnd n s0) J := by
      dsimp [t]
      omega
    have hend : 0 < coldEnd n s0 := coldEnd_pos hn hs0
    have hchunk : adaptivePhaseChunk N (coldEnd n s0) t < J :=
      adaptivePhaseChunk_lt_of_lt_offset hN hend ht
    have hlocal := adaptiveLocalPhase_lt hN hend t
    have hphase := adaptiveChunk_phase_lt_two hN hend hlocal
    have hsigma : adaptiveSigmaSq N (coldEnd n s0) t < 2 * N := by
      simpa [adaptiveSigmaSq] using
        hphase.trans_le (mul_le_mul_of_nonneg_left (hbelow _ hchunk) (by norm_num))
    rw [phaseVarFactor, if_neg hicold]
    unfold adaptiveGlobalPhaseVarFactor
    have hkN : 0 < k * N := mul_pos hk hN
    rw [add_le_add_iff_left]
    rw [div_le_div_iff₀ hkN hk]
    change adaptiveSigmaSq N (coldEnd n s0) t * k ≤ 8 * (k * N)
    nlinarith

/-- Extend the active hybrid factors by the corrected bundle's conservative factor. -/
noncomputable def correctedHybridFactor
    (n m : Nat) (k N s0 : Real) (i : Nat) : Real :=
  if i < m then phaseVarFactor n k N s0 i else 1 + 8 / k

theorem correctedHybridFactor_le {J m i : Nat} (hn : 1 ≤ n)
    {k N s0 : Real} (hk : 0 < k) (hN : 0 < N) (hs0 : 0 < s0)
    (hm : m = coldPhases n s0 + adaptiveChunkOffset N (coldEnd n s0) J)
    (hbelow : ∀ j < J, adaptiveChunkStart N (coldEnd n s0) j ≤ N) :
    correctedHybridFactor n m k N s0 i ≤ 1 + 8 / k := by
  unfold correctedHybridFactor
  split_ifs with hi
  · apply phaseVarFactor_le_one_add_eight_div hn hk hN hs0 hbelow
    simpa [hm] using hi
  · exact le_rfl

/-- One named operational hypothesis for all phases of corrected hybrid accuracy.

`proposalFor i S` is a *law*, regenerated afresh on every rejection retry.  The
`regeneration` field records both its origin from the conditioned history and the actual
joint-law factorization. -/
structure HybridFreshOperational
    {Ω Hist E : Type*} [MeasurableSpace Ω] [MeasurableSpace Hist]
    [MeasurableSpace E]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (V : Nat → Ω → Real) (m : Nat) (eta : Real)
    (H : Nat → Ω → Hist) (Y : Nat → Ω → Space n)
    (last : Hist → E) (proposalLaw : Nat → Measure E → Measure E)
    (proposalFor : Nat → Set Hist → ProbabilityMeasure E)
    (A : Nat → Set E) (f : Nat → E → Space n)
    (c s : Nat → Real) (epsPhase : Nat → ENNReal)
    (tau : Nat → Measure (Space n)) [∀ i, IsProbabilityMeasure (tau i)] where
  measurable_H : ∀ i, Measurable (H i)
  measurable_Y : ∀ i, Measurable (Y i)
  measurable_A : ∀ i, MeasurableSet (A i)
  measurable_f : ∀ i, Measurable (f i)
  s_pos : ∀ i, 0 < s i
  c_sq_le : ∀ i, (c i) ^ 2 ≤ 1
  eps_ne_top : ∀ i, epsPhase i ≠ ⊤
  u : Nat → Hist → Real
  v : Nat → Space n → Real
  measurable_u : ∀ i, Measurable (u i)
  measurable_v : ∀ i, Measurable (v i)
  U_eq : ∀ i, accuracyU μ V (correctedAlpha m eta) i = fun ω => u i (H i ω)
  V_eq : ∀ i, V (i + 1) = fun ω => v i (Y i ω)
  regeneration : ∀ i, FreshRegenerationResource μ (H i) (Y i) last
    (proposalLaw i) (proposalFor i)
    (fun q => freshTwoStageSpeedyRestartKernel (measurable_A i)
      (f i) (measurable_f i) (c i) (s i) q)
  shrink_mass : ∀ i S, MeasurableSet S → 1 / 2 ≤ μ.real (H i ⁻¹' S) →
    (proposalFor i S : Measure E) (A i) ≠ 0
  accept_mass : ∀ i S, MeasurableSet S → 1 / 2 ≤ μ.real (H i ⁻¹' S) →
    ((Measure.map (f i) (Arlib.condOn (proposalFor i S : Measure E) (A i))).withDensity
      fun x => ENNReal.ofReal (Arlib.MarkovChains.speedyAcceptReal (c i) (s i) x))
      Set.univ ≠ 0
  target_tv : ∀ i S, MeasurableSet S → 1 / 2 ≤ μ.real (H i ⁻¹' S) →
    TVLe
      (Arlib.condOn
        ((Measure.map (f i) (Arlib.condOn (proposalFor i S : Measure E) (A i))).withDensity
          fun x => ENNReal.ofReal (Arlib.MarkovChains.speedyAcceptReal (c i) (s i) x))
        Set.univ)
      (tau i) (epsPhase i)
  dependence_budget : ∀ i,
    2 * (epsPhase i).toReal ≤ correctedNu m eta

/-- The operational package discharges both dependence premises of corrected accuracy. -/
theorem HybridFreshOperational.correctedDependencePremises
    {Ω Hist E : Type*} [MeasurableSpace Ω] [MeasurableSpace Hist]
    [MeasurableSpace E]
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {V : Nat → Ω → Real} {m : Nat} {eta : Real}
    {H : Nat → Ω → Hist} {Y : Nat → Ω → Space n}
    {last : Hist → E} {proposalLaw : Nat → Measure E → Measure E}
    {proposalFor : Nat → Set Hist → ProbabilityMeasure E}
    {A : Nat → Set E} {f : Nat → E → Space n}
    {c s : Nat → Real} {epsPhase : Nat → ENNReal}
    {tau : Nat → Measure (Space n)} [∀ i, IsProbabilityMeasure (tau i)]
    (hop : HybridFreshOperational μ V m eta H Y last proposalLaw proposalFor
      A f c s epsPhase tau) :
    (∀ i, NuIndep μ (accuracyU μ V (correctedAlpha m eta) i) (V (i + 1))
      (correctedNu m eta)) ∧
    (∀ i, NuIndep μ
      (fun ω => (accuracyU μ V (correctedAlpha m eta) i ω) ^ 2)
      (fun ω => (V (i + 1) ω) ^ 2) (correctedNu m eta)) := by
  apply correctedAccuracy_dependencePremises_of_freshRegeneration V H Y hop.u hop.v
    hop.U_eq hop.V_eq epsPhase hop.dependence_budget
  intro i
  exact nuIndep_statistics_and_sq_of_freshTwoStageRegeneration
    (hop.measurable_H i) (hop.measurable_Y i) last (proposalLaw i) (proposalFor i)
    (hop.measurable_A i) (hop.measurable_f i) (hop.s_pos i) (hop.c_sq_le i)
    (hop.eps_ne_top i) (hop.regeneration i) (hop.shrink_mass i)
    (hop.accept_mass i) (hop.target_tv i) (hop.u i) (hop.v i)
    (hop.measurable_u i) (hop.measurable_v i)

/-- Corrected one-run hybrid accuracy together with the exact cold/hot factor-product
budget.  All path semantics are contained in the single `hop` argument. -/
theorem corrected_hybrid_accuracy
    {Ω Hist E : Type*} [MeasurableSpace Ω] [MeasurableSpace Hist]
    [MeasurableSpace E]
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    (V Wbar W : Nat → Ω → Real) {m k J n : Nat} {eta : Real}
    {N s0 kappaCold kappaHot : Real}
    (hn : 1 ≤ n) (hkpos : 0 < (k : Real)) (hk42 : 42 ≤ (k : Real))
    (hN : 0 < N) (hs0 : 0 < s0)
    (hm : m = coldPhases n s0 + adaptiveChunkOffset N (coldEnd n s0) J)
    (hcoldBudget : 2 * (coldPhases n s0 : Real) / (n : Real) ≤ k * kappaCold)
    (hbelow : ∀ j < J, adaptiveChunkStart N (coldEnd n s0) j ≤ N)
    (hhotBudget : 7 * (J : Real) ≤ k * kappaHot)
    (heta : 0 < eta) (heta1 : eta ≤ 1) (hk : CorrectedSampleBudget m k eta)
    (hVm : ∀ j, Measurable (V j)) (hV0 : ∀ j ω, 0 ≤ V j ω)
    (hEpos : ∀ j, 0 < ∫ ω, V j ω ∂μ)
    (hVcap : ∀ j ω, V j ω ≤ 2 * correctedAlpha m eta * ∫ z, V j z ∂μ)
    (hV2 : ∀ j, Integrable (fun ω => (V j ω) ^ 2) μ)
    (hV2cap : ∀ j ω, (V j ω) ^ 2 ≤
      2 * correctedAlpha m eta ^ 2 * ∫ z, (V j z) ^ 2 ∂μ)
    (hWm : ∀ j, Measurable (Wbar j)) (hW0 : ∀ j ω, 0 ≤ Wbar j ω)
    (hWint : ∀ j, Integrable (Wbar j) μ)
    (hWEpos : ∀ j, 0 < ∫ ω, Wbar j ω ∂μ)
    (hVdef : ∀ j ω, V j ω = min (Wbar j ω)
      (correctedAlpha m eta * ∫ z, Wbar j z ∂μ))
    (hphaseMoment : ∀ j,
      (∫ ω, (V j ω) ^ 2 ∂μ) ≤ correctedHybridFactor n m k N s0 j *
        (∫ ω, V j ω ∂μ) ^ 2)
    {Eexact : Set Ω} (hEexact : MeasurableSet Eexact)
    (hExactFail : μ.real Eexactᶜ ≤ 1 / 20)
    (hExact : ∀ ω ∈ Eexact, phaseProduct Wbar m ω = phaseProduct W m ω)
    {H : Nat → Ω → Hist} {Y : Nat → Ω → Space n}
    {last : Hist → E} {proposalLaw : Nat → Measure E → Measure E}
    {proposalFor : Nat → Set Hist → ProbabilityMeasure E}
    {A : Nat → Set E} {f : Nat → E → Space n}
    {c s : Nat → Real} {epsPhase : Nat → ENNReal}
    {tau : Nat → Measure (Space n)} [∀ i, IsProbabilityMeasure (tau i)]
    (hop : HybridFreshOperational μ V m eta H Y last proposalLaw proposalFor
      A f c s epsPhase tau) :
    μ.real {ω | phaseProduct W m ω ∉ relErr eta (prefixMean μ V m)} ≤ 1 / 5 ∧
      (∏ i ∈ Finset.range m, phaseVarFactor n k N s0 i) ≤
        Real.exp (kappaCold + kappaHot) := by
  have hdeps := hop.correctedDependencePremises
  have hratio : ∀ j,
      (∫ ω, (V j ω) ^ 2 ∂μ) ≤
        (1 + 8 / (k : Real)) * (∫ ω, V j ω ∂μ) ^ 2 := by
    intro j
    exact (hphaseMoment j).trans (mul_le_mul_of_nonneg_right
      (correctedHybridFactor_le hn hkpos hN hs0 hm hbelow) (sq_nonneg _))
  constructor
  · exact corrected_lem_accuracy_concrete V Wbar W heta heta1 hk hVm hV0 hEpos
      hVcap hV2 hV2cap hdeps.1 hdeps.2 hWm hW0 hWint hWEpos hVdef hratio
      hEexact hExactFail hExact
  · rw [hm]
    exact prod_phaseVarFactor_le_exp hn hk42 hN hs0 hcoldBudget hbelow hhotBudget

/-! Axiom audit. -/

#print axioms phaseVarFactor_le_one_add_eight_div
#print axioms HybridFreshOperational.correctedDependencePremises
#print axioms corrected_hybrid_accuracy

end Ttc.CVHybridCorrected

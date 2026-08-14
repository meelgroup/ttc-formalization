/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import Ttc.Volume.CVConcreteOracleAccuracy
import Ttc.Volume.RunwiseSamplerAmplification

/-!
# Runwise accuracy for the concrete adaptive terminal sampler

The exact adaptive terminal estimator is first analyzed for one run, at success `4/5`.
The cold normalizer is then replaced pointwise inside that one-run success event.  Finally,
sampler TV is spent only over the coordinates of that run and iid median amplification is
applied.  The sampler budget is therefore independent of the requested failure probability.
-/

namespace Ttc.CVAdaptive

open MeasureTheory ProbabilityTheory Metric Set
open Arlib Arlib.Probability Arlib.GaussianCooling
open Arlib.GaussianCooling.Chunked
open Ttc.CV.Adaptive
open scoped ENNReal

variable {n m r k J : Nat}

/-- The empirical phase average as a function on a single run. -/
noncomputable def oneRunPhaseAvg {E : Type*} (k : Nat)
    (g : Fin m -> Fin k -> E -> Real) (i : Fin m)
    (omega : Fin m -> Fin k -> E) : Real :=
  Ttc.CVEst.avgOf k (fun l omega' => g i l (omega' i l)) omega

theorem measurable_oneRunPhaseAvg {E : Type*} [MeasurableSpace E]
    {g : Fin m -> Fin k -> E -> Real} (hg : forall i l, Measurable (g i l)) (i : Fin m) :
    Measurable (oneRunPhaseAvg k g i) := by
  unfold oneRunPhaseAvg Ttc.CVEst.avgOf
  exact (Finset.measurable_fun_sum _ fun l _ =>
    (hg i l).comp ((measurable_pi_apply l).comp (measurable_pi_apply i))).div
      measurable_const

/-- One exact adaptive terminal run succeeds with probability `4/5`.  This is the
single-run core of `packed_median_accuracy_adaptive_terminal_exact`; the moment and schedule
arguments are the same, but no repetition count or failure probability occurs. -/
theorem oneRun_accuracy_adaptive_terminal_exact (hn : 2 <= n) (hk : 0 < k)
    {K : Set (Space n)} (hKc : Convex Real K) (hKcl : IsClosed K)
    (hKb : Bornology.IsBounded K) (hvol : 0 < volume K)
    (hball : ball (0 : Space n) 1 ⊆ K) (hfin : volume K ≠ ⊤)
    {C s0 kappa eps : Real} (hC : 0 < C) (hs0 : 0 < s0) (hkappa : 0 <= kappa)
    (heps : 0 < eps) (hk42 : 42 <= (k : Real))
    (hbelow : forall j, j < J -> adaptiveChunkStart (C ^ 2 * n) s0 j <= C ^ 2 * n)
    (hterminal : C ^ 2 * n <= adaptiveChunkStart (C ^ 2 * n) s0 J)
    (hsamples : 7 * (J : Real) <= (k : Real) * kappa)
    (hKR : K ⊆ closedBall 0 (C * Real.sqrt n))
    (hbudget : Real.exp (kappa + (Real.exp (1 / 2) - 1) / (k : Real)) - 1 <=
      eps ^ 2 / 5) :
    let N : Real := C ^ 2 * n
    let m := adaptiveChunkOffset N s0 J
    let sigmaSq := adaptiveSigmaSq N s0
    let nu : Fin (m + 1) -> Fin k -> Measure (Space n) :=
      fun i _ => coolLaw (m + 1) sigmaSq K i
    let g : Fin (m + 1) -> Fin k -> Space n -> Real :=
      fun i _ => phaseScore (m + 1) sigmaSq K i
    4 / 5 <= (Ttc.CVRunwise.oneRunLaw nu).real
      {omega | chain (m + 1) sigmaSq K 0 *
        ∏ i, oneRunPhaseAvg k g i omega ∈ Ttc.relErr eps (volume K).toReal} := by
  dsimp only
  let N : Real := C ^ 2 * n
  let m := adaptiveChunkOffset N s0 J
  let sigmaSq := adaptiveSigmaSq N s0
  let nu : Fin (m + 1) -> Fin k -> Measure (Space n) :=
    fun i _ => coolLaw (m + 1) sigmaSq K i
  let nuPacked : Fin 1 -> Fin (m + 1) -> Fin k -> Measure (Space n) :=
    fun _ i l => nu i l
  let g : Fin (m + 1) -> Fin k -> Space n -> Real :=
    fun i _ => phaseScore (m + 1) sigmaSq K i
  let gPacked : Fin 1 -> Fin (m + 1) -> Fin k -> Space n -> Real :=
    fun _ i l => g i l
  let c : Fin (m + 1) -> Real := fun i =>
    if hi : (i : Nat) < m then adaptiveGlobalPhaseVarFactor 1 N s0 i
    else Real.exp (1 / 2)
  let kappaTot : Real := kappa + (Real.exp (1 / 2) - 1) / (k : Real)
  have hnpos : (0 : Real) < n := by exact_mod_cast (show 0 < n by omega)
  have hN : 0 < N := by dsimp [N]; positivity
  have hsigma : forall q, 0 < sigmaSq q := fun q => adaptiveSigmaSq_pos hN hs0 q
  letI hnuProb : ∀ i l, IsProbabilityMeasure (nu i l) := fun i l => by
    dsimp only [nu]
    exact coolLaw_isProbabilityMeasure hsigma hball hfin i
  letI hnuPackedProb : ∀ t i l, IsProbabilityMeasure (nuPacked t i l) :=
    fun _ i l => hnuProb i l
  letI (i : Fin (m + 1)) (l : Fin k) : IsProbabilityMeasure (nu i l) := hnuProb i l
  letI (t : Fin 1) (i : Fin (m + 1)) (l : Fin k) :
      IsProbabilityMeasure (nuPacked t i l) := hnuPackedProb t i l
  letI hpackedProb : ∀ t i, IsProbabilityMeasure (packedPhaseLaw nuPacked t i) :=
    fun t i => @packedPhaseLaw_isProbabilityMeasure 1 (m + 1) k (Space n) _ nuPacked
      hnuPackedProb t i
  let mu := Arlib.Probability.runMeasure (packedPhaseLaw nuPacked)
  haveI : IsProbabilityMeasure mu := by
    unfold mu Arlib.Probability.runMeasure
    infer_instance
  have hg : forall t i l, Measurable (gPacked t i l) := by
    intro t i l
    exact measurable_phaseScore hKcl.measurableSet i
  have hscoreBound : forall t i l x,
      |gPacked t i l x| <= Real.exp ((C * Real.sqrt n) ^ 2 / (2 * sigmaSq i)) := by
    intro t i l x
    rw [abs_of_nonneg (phaseScore_nonneg (m + 1) sigmaSq K i x)]
    exact phaseScore_le hsigma hKR i x
  have hL2marg : forall t i l, MemLp (gPacked t i l) 2 (nuPacked t i l) := by
    intro t i l
    letI : IsProbabilityMeasure (nuPacked t i l) := hnuPackedProb t i l
    exact MemLp.of_bound (hg t i l).aestronglyMeasurable
      (Real.exp ((C * Real.sqrt n) ^ 2 / (2 * sigmaSq i)))
      (Filter.Eventually.of_forall fun x => by
        simpa [Real.norm_eq_abs] using hscoreBound t i l x)
  let t0 : Fin 1 := 0
  let Y := Ttc.CVPacked.sampleScore gPacked t0
  have hL2 : forall i l, MemLp (Y i l) 2 mu := fun i l =>
    @Ttc.CVPacked.memLp_sampleScore 1 (m + 1) k (Space n) _ nuPacked
      hnuPackedProb gPacked t0 i l (hL2marg t0 i l)
  have hindep : Ttc.CVEst.CoordinateIndep Y mu :=
    @Ttc.CVPacked.coordinateIndep_sampleScore 1 (m + 1) k (Space n) _ nuPacked
      hnuPackedProb gPacked hg t0
  have hprod : MemLp (fun omega => ∏ i, Ttc.CVPacked.phaseAvg gPacked t0 i omega) 2 mu := by
    let B : Real := ∏ i : Fin (m + 1),
      Real.exp ((C * Real.sqrt n) ^ 2 / (2 * sigmaSq i))
    have hmeas : Measurable (fun omega =>
        ∏ i, Ttc.CVPacked.phaseAvg gPacked t0 i omega) :=
      Finset.measurable_fun_prod _ fun i _ => Ttc.CVPacked.measurable_phaseAvg hg t0 i
    refine MemLp.of_bound hmeas.aestronglyMeasurable B ?_
    filter_upwards with omega
    rw [Real.norm_eq_abs, Finset.abs_prod]
    have havg : forall i : Fin (m + 1),
        |Ttc.CVPacked.phaseAvg gPacked t0 i omega| <=
          Real.exp ((C * Real.sqrt n) ^ 2 / (2 * sigmaSq i)) := by
      intro i
      unfold Ttc.CVPacked.phaseAvg Ttc.CVEst.avgOf
      rw [abs_div]
      have hkR : (0 : Real) < k := by exact_mod_cast hk
      rw [abs_of_pos hkR, div_le_iff₀ hkR]
      calc
        |∑ l, Ttc.CVPacked.sampleScore gPacked t0 i l omega| <=
            ∑ l, |Ttc.CVPacked.sampleScore gPacked t0 i l omega| :=
          Finset.abs_sum_le_sum_abs _ _
        _ <= ∑ _l : Fin k,
            Real.exp ((C * Real.sqrt n) ^ 2 / (2 * sigmaSq i)) := by
          apply Finset.sum_le_sum
          intro l _
          exact hscoreBound t0 i l _
        _ = (k : Real) * Real.exp ((C * Real.sqrt n) ^ 2 / (2 * sigmaSq i)) := by
          simp
        _ = Real.exp ((C * Real.sqrt n) ^ 2 / (2 * sigmaSq i)) * (k : Real) := by
          ring
    exact Finset.prod_le_prod (fun i _ => abs_nonneg _) fun i _ =>
      havg i
  have hmean : forall i l, ∫ omega, Y i l omega ∂mu =
      chain (m + 1) sigmaSq K ((i : Nat) + 1) / chain (m + 1) sigmaSq K i := by
    intro i l
    rw [@Ttc.CVPacked.integral_sampleScore 1 (m + 1) k (Space n) _ nuPacked
      hnuPackedProb gPacked hg t0 i l]
    exact integral_phaseScore_coolLaw hKcl.measurableSet (chain_pos hsigma hball hfin i)
  have hterminalSigma : N <= sigmaSq m := by
    change N <= adaptiveSigmaSq N s0 (adaptiveChunkOffset N s0 J)
    rw [adaptiveSigmaSq_offset hN hs0 J]
    simpa only [N] using hterminal
  have hR2 : (C * Real.sqrt n) ^ 2 <= sigmaSq m := by
    have hsqrt : Real.sqrt (n : Real) ^ 2 = n := Real.sq_sqrt hnpos.le
    rw [mul_pow, hsqrt]
    simpa only [N] using hterminalSigma
  have hsqMarg : forall i l, ∫ x, (g i l x) ^ 2 ∂(nu i l) <=
      c i * (chain (m + 1) sigmaSq K ((i : Nat) + 1) /
        chain (m + 1) sigmaSq K i) ^ 2 := by
    intro i l
    by_cases hi : (i : Nat) < m
    · let i' : Fin m := ⟨i, hi⟩
      have hphase := Ttc.CV.adaptivePhaseScore_sq_moment_le hn hKc hKcl hKb hvol
        hball hfin hC hs0 hbelow hKR i'
      rw [integral_phaseScore_coolLaw hKcl.measurableSet
        (chain_pos hsigma hball hfin i')] at hphase
      simpa only [nu, g, c, hi, dif_pos, i'] using hphase
    · have him : (i : Nat) = m := by omega
      have hilast : i = Fin.last m := by apply Fin.ext; simpa using him
      subst i
      have hterm := coolLaw_sq_moment_le_terminal_paper (m := m + 1) hsigma
        hKcl.measurableSet hball hfin hKR (i := m) le_rfl hR2
      rw [integral_phaseScore_coolLaw hKcl.measurableSet
        (chain_pos hsigma hball hfin m)] at hterm
      change ∫ x, phaseScore (m + 1) sigmaSq K m x ^ 2
          ∂(coolLaw (m + 1) sigmaSq K m) <=
        c (Fin.last m) *
          (chain (m + 1) sigmaSq K (m + 1) / chain (m + 1) sigmaSq K m) ^ 2
      rw [show c (Fin.last m) = Real.exp (1 / 2) by simp [c]]
      exact hterm
  have hsq : forall i l, ∫ omega, (Y i l omega) ^ 2 ∂mu <=
      c i * (chain (m + 1) sigmaSq K ((i : Nat) + 1) /
        chain (m + 1) sigmaSq K i) ^ 2 := by
    intro i l
    have hmeasSq : forall t i l, Measurable (fun x => (gPacked t i l x) ^ 2) :=
      fun t i l => (hg t i l).pow_const 2
    have heq := @Ttc.CVPacked.integral_sampleScore 1 (m + 1) k (Space n) _ nuPacked
      hnuPackedProb (fun t i l x => (gPacked t i l x) ^ 2) hmeasSq t0 i l
    change (∫ omega, (Y i l omega) ^ 2 ∂mu) =
      ∫ x, (g i l x) ^ 2 ∂(nu i l) at heq
    rw [heq]
    exact hsqMarg i l
  have hinterior : (∏ i : Fin m,
      (1 + (adaptiveGlobalPhaseVarFactor 1 N s0 i - 1) / (k : Real))) <=
      Real.exp kappa := by
    simp_rw [Ttc.CVEst.averaged_adaptiveGlobalPhaseVarFactor_eq]
    rw [Fin.prod_univ_eq_prod_range]
    exact prod_globalPhaseVarFactor_le_exp hk42 hN hs0 hbelow hsamples
  have htermExcess : 0 <= (Real.exp (1 / 2) - 1) / (k : Real) :=
    div_nonneg (by linarith [Real.add_one_le_exp (1 / 2 : Real)]) (by positivity)
  have hfactor : (∏ i : Fin (m + 1), (1 + (c i - 1) / (k : Real))) <=
      Real.exp kappaTot := by
    rw [Fin.prod_univ_castSucc]
    have hcast : (∏ i : Fin m, (1 + (c i.castSucc - 1) / (k : Real))) =
        ∏ i : Fin m,
          (1 + (adaptiveGlobalPhaseVarFactor 1 N s0 i - 1) / (k : Real)) := by
      apply Finset.prod_congr rfl
      intro i _
      simp only [c, Fin.val_castSucc, i.isLt, dif_pos]
    rw [hcast, show c (Fin.last m) = Real.exp (1 / 2) by simp [c]]
    calc
      (∏ i : Fin m,
          (1 + (adaptiveGlobalPhaseVarFactor 1 N s0 i - 1) / (k : Real))) *
          (1 + (Real.exp (1 / 2) - 1) / (k : Real)) <=
          Real.exp kappa * Real.exp ((Real.exp (1 / 2) - 1) / (k : Real)) := by
            gcongr
            simpa [add_comm] using
              (Real.add_one_le_exp ((Real.exp (1 / 2) - 1) / (k : Real)))
      _ = Real.exp kappaTot := by rw [← Real.exp_add]
  have hkappaTot : 0 <= kappaTot := add_nonneg hkappa htermExcess
  have hgood : 4 / 5 <= mu.real
      {omega | chain (m + 1) sigmaSq K 0 *
        ∏ i, Ttc.CVPacked.phaseAvg gPacked t0 i omega ∈
          Ttc.relErr eps (volume K).toReal} := by
    rw [← chain_end (m + 1) sigmaSq K]
    exact Ttc.CVEst.run_four_fifths_exact_of_factorProduct hk hkappaTot heps
      (fun q => chain_pos hsigma hball hfin q) hL2 hindep hprod hmean hsq hfactor hbudget
  have hcoord : MeasurePreserving
      (fun omega : Fin 1 -> Fin (m + 1) -> Fin k -> Space n => omega t0)
      mu (Ttc.CVRunwise.oneRunLaw nu) := by
    haveI hone : IsProbabilityMeasure (Ttc.CVRunwise.oneRunLaw nu) :=
      @Ttc.CVRunwise.oneRunLaw_isProbabilityMeasure (Space n) _ (m + 1) k nu hnuProb
    letI : ∀ _ : Fin 1, IsProbabilityMeasure (Ttc.CVRunwise.oneRunLaw nu) :=
      fun _ => hone
    have hmp := measurePreserving_eval
      (fun _ : Fin 1 => Ttc.CVRunwise.oneRunLaw nu) t0
    simpa only [mu, Arlib.Probability.runMeasure, packedPhaseLaw, nuPacked,
      Ttc.CVRunwise.oneRunLaw] using hmp
  have hV : Measurable (fun omega : Fin (m + 1) -> Fin k -> Space n =>
      chain (m + 1) sigmaSq K 0 * ∏ i, oneRunPhaseAvg k g i omega) :=
    measurable_const.mul (Finset.measurable_fun_prod _ fun i _ =>
      measurable_oneRunPhaseAvg (fun i l => measurable_phaseScore hKcl.measurableSet i) i)
  have hS : MeasurableSet {omega : Fin (m + 1) -> Fin k -> Space n |
      chain (m + 1) sigmaSq K 0 * ∏ i, oneRunPhaseAvg k g i omega ∈
        Ttc.relErr eps (volume K).toReal} := hV measurableSet_Icc
  have hmap := hcoord.map_eq
  change 4 / 5 <= (Ttc.CVRunwise.oneRunLaw nu).real
    {omega | chain (m + 1) sigmaSq K 0 * ∏ i, oneRunPhaseAvg k g i omega ∈
      Ttc.relErr eps (volume K).toReal}
  rw [← hmap]
  change 4 / 5 <= ((Measure.map (fun omega => omega t0) mu)
    {omega | chain (m + 1) sigmaSq K 0 * ∏ i, oneRunPhaseAvg k g i omega ∈
      Ttc.relErr eps (volume K).toReal}).toReal
  rw [Measure.map_apply hcoord.measurable hS]
  have hpre : ((fun omega : Fin 1 -> Fin (m + 1) -> Fin k -> Space n => omega t0) ⁻¹'
      {omega | chain (m + 1) sigmaSq K 0 * ∏ i, oneRunPhaseAvg k g i omega ∈
        Ttc.relErr eps (volume K).toReal}) =
      {omega | chain (m + 1) sigmaSq K 0 *
        ∏ i, Ttc.CVPacked.phaseAvg gPacked t0 i omega ∈
          Ttc.relErr eps (volume K).toReal} := by
    ext omega
    rfl
  rw [hpre]
  exact hgood

/-- First-terminal specialization of the one-run exact theorem. -/
theorem oneRun_accuracy_adaptive_first_terminal_exact
    (hn : 2 <= n) (hk : 0 < k)
    {K : Set (Space n)} (hKc : Convex Real K) (hKcl : IsClosed K)
    (hKb : Bornology.IsBounded K) (hvol : 0 < volume K)
    (hball : ball (0 : Space n) 1 ⊆ K) (hfin : volume K ≠ ⊤)
    {C s0 kappa eps : Real} (hC : 0 < C) (hs0 : 0 < s0) (hkappa : 0 <= kappa)
    (heps : 0 < eps) (hk42 : 42 <= (k : Real))
    (hsamples : 7 * (adaptiveTerminalChunk (C ^ 2 * n) s0 : Real) <=
      (k : Real) * kappa)
    (hKR : K ⊆ closedBall 0 (C * Real.sqrt n))
    (hbudget : Real.exp (kappa + (Real.exp (1 / 2) - 1) / (k : Real)) - 1 <=
      eps ^ 2 / 5) :
    let N : Real := C ^ 2 * n
    let J := adaptiveTerminalChunk N s0
    let m := adaptiveChunkOffset N s0 J
    let sigmaSq := adaptiveSigmaSq N s0
    let nu : Fin (m + 1) -> Fin k -> Measure (Space n) :=
      fun i _ => coolLaw (m + 1) sigmaSq K i
    let g : Fin (m + 1) -> Fin k -> Space n -> Real :=
      fun i _ => phaseScore (m + 1) sigmaSq K i
    4 / 5 <= (Ttc.CVRunwise.oneRunLaw nu).real
      {omega | chain (m + 1) sigmaSq K 0 * ∏ i, oneRunPhaseAvg k g i omega ∈
        Ttc.relErr eps (volume K).toReal} := by
  dsimp only
  let N : Real := C ^ 2 * n
  have hN : 0 < N := by dsimp [N]; positivity
  have hbelow : forall j, j < adaptiveTerminalChunk N s0 ->
      adaptiveChunkStart N s0 j <= N := by
    intro j hj
    exact (adaptiveChunkStart_lt_target_of_lt_terminal hN hs0 hj).le
  have hterminal : N <= adaptiveChunkStart N s0 (adaptiveTerminalChunk N s0) :=
    target_le_adaptiveTerminalChunk hN hs0
  exact oneRun_accuracy_adaptive_terminal_exact hn hk hKc hKcl hKb hvol hball hfin
    hC hs0 hkappa heps hk42 hbelow hterminal hsamples hKR hbudget

/-! ## Cold correction, runwise TV transfer, and iid amplification -/

/-- Generic source-faithful terminal composition.  The exact `4/5` statement is for one
run and the unknown restricted normalizer `A0`.  Cold-normalizer replacement is performed
inside that one-run event, sampler TV is then tensorized over only `m*k` coordinates, and
the approximate runs are finally repeated iid. -/
theorem median_accuracy_runwise_of_exact_and_cold
    {m k r : Nat} {E : Type*} [MeasurableSpace E]
    {nu nuExact : Fin m -> Fin k -> Measure E}
    [forall i l, IsProbabilityMeasure (nu i l)]
    [forall i l, IsProbabilityMeasure (nuExact i l)]
    {g : Fin m -> Fin k -> E -> Real}
    (hg : forall i l, Measurable (g i l)) (hg0 : forall i l x, 0 <= g i l x)
    (hk : 0 < k) {A0 Z0 V eps eta : Real}
    (hA0 : 0 < A0) (_hZ0 : 0 < Z0) (heps0 : 0 <= eps)
    (heta0 : 0 <= eta) (heta1 : eta < 1)
    (hA0le : A0 <= Z0) (hcold : A0 ∈ Ttc.relErr eta Z0)
    {b : ENNReal} (hb : b ≠ ⊤)
    (htv : forall i l, TVLe (nu i l) (nuExact i l) b)
    (hsampler : ((m * k : Nat) : Real) * b.toReal <= 1 / 10)
    (hexact : 4 / 5 <= (Ttc.CVRunwise.oneRunLaw nuExact).real
      {omega | A0 * ∏ i, oneRunPhaseAvg k g i omega ∈ Ttc.relErr eps V})
    (hr : 0 < r) {p : Real} (hp : 0 < p)
    (hrp : Real.log (1 / p) / (2 * (7 / 10 - 1 / 2) ^ 2) <= (r : Real)) :
    1 - p <=
      (Arlib.Probability.runMeasure
        (packedPhaseLaw (Ttc.CVRunwise.iidRunFamily (r := r) nu))).real
        {omega | medianSel (fun t =>
          Z0 * ∏ i, oneRunPhaseAvg k g i (omega t)) ∈
            Ttc.relErr ((eps + eta) / (1 - eta)) V} := by
  let X : (Fin m -> Fin k -> E) -> Real := fun omega =>
    ∏ i, oneRunPhaseAvg k g i omega
  have hXmeas : Measurable X :=
    Finset.measurable_fun_prod _ fun i _ => measurable_oneRunPhaseAvg hg i
  have hX0 : forall omega, 0 <= X omega := by
    intro omega
    apply Finset.prod_nonneg
    intro i _
    unfold oneRunPhaseAvg Ttc.CVEst.avgOf
    exact div_nonneg (Finset.sum_nonneg fun l _ => hg0 i l _) (by positivity)
  have hexactZ : 4 / 5 <= (Ttc.CVRunwise.oneRunLaw nuExact).real
      {omega | Z0 * X omega ∈ Ttc.relErr ((eps + eta) / (1 - eta)) V} := by
    refine hexact.trans (measureReal_mono ?_)
    intro omega homega
    exact Ttc.CV.mem_relErr_replace_coldNormalizer hA0 (hX0 omega) heps0 heta0 heta1
      hA0le hcold homega
  have hVZ : Measurable (fun omega => Z0 * X omega) := measurable_const.mul hXmeas
  have hmain := Ttc.CVRunwise.median_success_of_runwise_sampler_tv
    (r := r) hb htv hsampler hVZ hexactZ hr hp hrp
  simpa only [X] using hmain

/-- Concrete first-terminal adaptive sampler, with sampler accuracy paid once per run.
The mixing error premise is `((m+1)*k)*b ≤ 1/10`; requested confidence `p` occurs only
in the iid repetition lower bound. -/
theorem median_accuracy_concrete_adaptive_runwise
    (hn : 21 <= n) (hk : 0 < k) (hr : 0 < r)
    {K : Set (Space n)} (hKc : Convex Real K) (hKcl : IsClosed K)
    (hKb : Bornology.IsBounded K) (hvol : 0 < volume K)
    (hclosedBall : closedBall (0 : Space n) 1 ⊆ K) (hfin : volume K ≠ ⊤)
    {C kappa epsEst eta p epsMix : Real}
    (hC : 0 < C) (hkappa : 0 <= kappa) (hepsEst : 0 < epsEst)
    (heta : 0 < eta) (heta1 : eta < 1)
    (hk42 : 42 <= (k : Real))
    (hsamples : 7 * (adaptiveTerminalChunk (C ^ 2 * n)
      (endpointSigmaSq n eta) : Real) <= (k : Real) * kappa)
    (hKR : K ⊆ closedBall 0 (C * Real.sqrt n))
    (hbudget : Real.exp (kappa + (Real.exp (1 / 2) - 1) / (k : Real)) - 1 <=
      epsEst ^ 2 / 5)
    (hp : 0 < p)
    (hrp : Real.log (1 / p) / (2 * (7 / 10 - 1 / 2) ^ 2) <= (r : Real))
    (hepsMix0 : 0 < epsMix) (hepsMix32 : epsMix <= 1 / 32)
    (steps : Fin (terminalPhaseCount n C (endpointSigmaSq n eta) + 1) -> Nat)
    (hsteps : forall i : Fin (terminalPhaseCount n C (endpointSigmaSq n eta) + 1),
      ¬ 4 * (n : Real) * terminalSigmaSq n C (endpointSigmaSq n eta) i <= 1 ->
      4 * 640 ^ 2 * adaptiveTerminalSigma (terminalTarget n C)
          (endpointSigmaSq n eta) i ^ 2 * (n : Real) *
          (Real.log (adaptiveRestartWarmConst n i) + 2 * Real.log (1 / epsMix)) /
            (adaptiveTerminalDelta (n := n) (terminalTarget n C)
              (endpointSigmaSq n eta) i * Real.log 2) ^ 2 + 1 <= (steps i : Real))
    (hsampler :
      (((terminalPhaseCount n C (endpointSigmaSq n eta) + 1) * k : Nat) : Real) *
        (64 * ENNReal.ofReal epsMix +
          ENNReal.ofReal ((4 * Real.exp (-(15 : Real) / 2)) ^ n)).toReal <= 1 / 10) :
    let nu : Fin (terminalPhaseCount n C (endpointSigmaSq n eta) + 1) ->
        Fin k -> Measure (Space n) :=
      fun i _ => adaptiveTerminalWarmLaw (terminalTarget n C) (endpointSigmaSq n eta)
        endpointRho K steps i
    let g : Fin (terminalPhaseCount n C (endpointSigmaSq n eta) + 1) ->
        Fin k -> Space n -> Real :=
      fun i _ => phaseScore (terminalPhaseCount n C (endpointSigmaSq n eta) + 1)
        (terminalSigmaSq n C (endpointSigmaSq n eta)) K i
    1 - p <=
      (runMeasure (packedPhaseLaw (Ttc.CVRunwise.iidRunFamily (r := r) nu))).real
        {omega | medianSel (fun t =>
          (2 * Real.pi * endpointSigmaSq n eta) ^ ((n : Real) / 2) *
            ∏ i, oneRunPhaseAvg k g i (omega t)) ∈
          Ttc.relErr ((epsEst + eta) / (1 - eta)) (volume K).toReal} := by
  dsimp only
  let N : Real := C ^ 2 * n
  let s0 : Real := endpointSigmaSq n eta
  let J := adaptiveTerminalChunk N s0
  let m := adaptiveChunkOffset N s0 J
  let sigmaSq := adaptiveSigmaSq N s0
  let nu : Fin (m + 1) -> Fin k -> Measure (Space n) :=
    fun i _ => adaptiveTerminalWarmLaw N s0 endpointRho K steps i
  let nuExact : Fin (m + 1) -> Fin k -> Measure (Space n) :=
    fun i _ => coolLaw (m + 1) sigmaSq K i
  let g : Fin (m + 1) -> Fin k -> Space n -> Real :=
    fun i _ => phaseScore (m + 1) sigmaSq K i
  have hn2 : 2 <= n := by omega
  have hn1 : 1 <= n := by omega
  have hball : ball (0 : Space n) 1 ⊆ K := ball_subset_closedBall.trans hclosedBall
  have hN : 0 < N := by dsimp [N]; positivity
  have hs0 : 0 < s0 := endpointSigmaSq_pos heta
  have hsigma : forall q, 0 < sigmaSq q := fun q => adaptiveSigmaSq_pos hN hs0 q
  have hbelow : forall j, j + 1 < m + 1 ->
      adaptiveChunkStart N s0 (adaptivePhaseChunk N s0 j) <= N := by
    intro j hj
    have hjm : j < m := by omega
    have hchunk : adaptivePhaseChunk N s0 j < J :=
      adaptivePhaseChunk_lt_of_lt_offset hN hs0 hjm
    exact (adaptiveChunkStart_lt_target_of_lt_terminal hN hs0 hchunk).le
  have hcoldStart : 4 * (n : Real) * s0 <= endpointRho ^ 2 :=
    endpointSigmaSq_coldBall heta.le heta1.le
  have hrho : 0 < endpointRho := endpointRho_pos
  have hrhoc : endpointRho < 1 - 1 / (2 * (n : Real)) := endpointRho_lt_shrink hn2
  letI hnuProb : forall i l, IsProbabilityMeasure (nu i l) := fun i l =>
    isProbabilityMeasure_adaptiveTerminalWarmLaw hn hN hs0 hKcl.measurableSet hKc
      hclosedBall hfin hrho hrhoc hcoldStart hbelow hepsMix0 hepsMix32 steps hsteps i
  letI hnuExactProb : forall i l, IsProbabilityMeasure (nuExact i l) := fun i l => by
    dsimp only [nuExact]
    exact coolLaw_isProbabilityMeasure hsigma hball hfin i
  letI (i : Fin (m + 1)) (l : Fin k) : IsProbabilityMeasure (nu i l) :=
    hnuProb i l
  letI (i : Fin (m + 1)) (l : Fin k) : IsProbabilityMeasure (nuExact i l) :=
    hnuExactProb i l
  let b : ENNReal := 64 * ENNReal.ofReal epsMix +
    ENNReal.ofReal ((4 * Real.exp (-(15 : Real) / 2)) ^ n)
  have hb : b ≠ ⊤ := by
    dsimp [b]
    exact ENNReal.add_ne_top.2
      ⟨ENNReal.mul_ne_top (by norm_num) ENNReal.ofReal_ne_top, ENNReal.ofReal_ne_top⟩
  have htv : forall i l, TVLe (nu i l) (nuExact i l) b := by
    intro i l
    exact tvLe_adaptiveTerminalWarmLaw hn hN hs0 hKcl.measurableSet hKc hclosedBall
      hfin hrho hrhoc hcoldStart hbelow hepsMix0 hepsMix32 steps hsteps i
  have hg : forall i l, Measurable (g i l) := fun i l =>
    measurable_phaseScore hKcl.measurableSet i
  have hg0 : forall i l x, 0 <= g i l x := fun i l x =>
    phaseScore_nonneg (m + 1) sigmaSq K i x
  have hsigma0 : sigmaSq 0 = endpointSigmaSq n eta := by
    dsimp [sigmaSq, s0]
    simpa [adaptiveChunkStart] using adaptiveSigmaSq_offset hN hs0 0
  have hballRho : closedBall (0 : Space n) endpointRho ⊆ K :=
    (closedBall_subset_closedBall (by norm_num [endpointRho])).trans hclosedBall
  have hcoldPkg := chain_zero_explicit_endpoint_package (n := n) (eta := eta) (m := m + 1)
    (by omega) hsigma0 hKcl.measurableSet hfin hn1 hballRho heta heta1.le
  have hexact := oneRun_accuracy_adaptive_first_terminal_exact hn2 hk hKc hKcl hKb hvol
    hball hfin hC hs0 hkappa hepsEst hk42 hsamples hKR hbudget
  exact @median_accuracy_runwise_of_exact_and_cold (m + 1) k r (Space n) _
    nu nuExact hnuProb hnuExactProb g hg hg0 hk
    (chain (m + 1) sigmaSq K 0) ((2 * Real.pi * s0) ^ ((n : Real) / 2))
    (volume K).toReal epsEst eta
    (chain_pos hsigma hball hfin 0) (by positivity) hepsEst.le heta.le heta1
    hcoldPkg.1 hcoldPkg.2 b hb htv hsampler
    (by simpa only [N, s0, J, m, sigmaSq, nuExact, g] using hexact) hr p hp hrp

end Ttc.CVAdaptive

#print axioms Ttc.CVAdaptive.oneRun_accuracy_adaptive_terminal_exact
#print axioms Ttc.CVAdaptive.oneRun_accuracy_adaptive_first_terminal_exact
#print axioms Ttc.CVAdaptive.median_accuracy_runwise_of_exact_and_cold
#print axioms Ttc.CVAdaptive.median_accuracy_concrete_adaptive_runwise

import Ttc.Exec.CVColdHotReferenceCost
import Ttc.Exec.CVSourceReferenceTheorem11Arithmetic

/-!
# Honest radial-log envelope for the concrete CV hybrid schedule

The terminal hot-chunk index occurs once in the weighted sample numerator and once in
the accelerated proposal sum.  For the literal dyadic schedule these two occurrences
cost `sourceLogFactor N ^ 2`, where `N` is the terminal variance.  This file records that
factor explicitly instead of hiding it in a purported universal constant.

The resulting public contract differs from the displayed CV Theorem 1.1 shape only by
this radial polylogarithm.  The final section is an arithmetic constructor: any public
expected-query algorithm whose amplified execution fits the honest source envelope is
packaged into the corresponding theorem-level certificate.
-/

set_option autoImplicit false

namespace Ttc.CVRadialLogEnvelope

open MeasureTheory Set
open Ttc.CVSourcePolynomialCutoffCapstone
open Ttc.CVSourceTheorem11Arithmetic
open Ttc.CVColdHotReferenceCost
open Ttc.CVHybridSchedule
open Ttc.CVHybridSourceSharpEnvelope
open Ttc.CV.Adaptive
open Ttc.CVCostedRuntimeCutoff Ttc.CVCostedAdjustableOuterMedian
open Arlib Arlib.Probability Arlib.GaussianCooling
open Arlib.GaussianCooling.Chunked
open scoped ENNReal BigOperators

/-- The source one-run core with the two literal terminal-chunk logarithms exposed. -/
noncomputable def sourceRadialLogOneRunQueryCore
    (runtimeConstant : Real) (n : Nat) (radius eps N : Real) : Real :=
  sourceOneRunQueryCore runtimeConstant n radius eps * sourceLogFactor N ^ 2

set_option linter.unusedVariables false in
/-- **The radial-log one-run budget scalar.**

⚠ This was `sourceRadialLogOneRunQueryCore … / eps²` — the source core with the two terminal
chunk logarithms, divided by the estimator's `eps²`.  It is now the scalar alone, in step
with `Ttc.CVSourcePolynomialCutoffCapstone.sourceOneRunQueryEnvelope`; the two must agree in
form, because `sourceOneRunQueryEnvelope_effective_eq_radialLog` is what lets this family
reuse the generic cutoff and median implementation.  See `lean/PLAN-SHAPE.md`.

`sourceRadialLogOneRunQueryCore` itself is unchanged and is still the shaped quantity
`Ttc.CVHotRefreshHonestRuntime` compares against. -/
noncomputable def sourceRadialLogOneRunQueryEnvelope
    (runtimeConstant : Real) (n : Nat) (radius eps N : Real) : Real :=
  runtimeConstant * sourceLogFactor N ^ 2

noncomputable def sourceRadialLogOneRunQueryBudget
    (runtimeConstant : Real) (n : Nat) (radius eps N : Real) : ENNReal :=
  ENNReal.ofReal (sourceRadialLogOneRunQueryEnvelope runtimeConstant n radius eps N)

/-- Confidence-amplified real envelope, including the source cutoff slack. -/
noncomputable def sourceRadialLogAmplifiedQueryEnvelope
    (runtimeConstant : Real) (n : Nat) (radius eps N p : Real) : Real :=
  (8 * Real.log (1 / p) + 2) *
    (20 * (sourceRadialLogOneRunQueryEnvelope runtimeConstant n radius eps N + 1))

/-- Globally valid theorem-level shape for the concrete dyadic implementation. -/
noncomputable def cvRadialLogComplexityShapeClipped
    (n : Nat) (R2 eps p : Real) : Real :=
  cvComplexityShapeClipped n R2 eps p *
    sourceLogFactor (max 1 R2) ^ 2

theorem sourceLogFactor_mono_of_pos {x y : Real}
    (hx : 0 < x) (hxy : x ≤ y) : sourceLogFactor x ≤ sourceLogFactor y := by
  unfold sourceLogFactor
  exact max_le_max le_rfl (Real.log_le_log hx hxy)

theorem sourceRadialLogOneRunQueryEnvelope_nonneg
    {runtimeConstant : Real} (hconstant : 0 ≤ runtimeConstant)
    (n : Nat) (radius eps N : Real) :
    0 ≤ sourceRadialLogOneRunQueryEnvelope runtimeConstant n radius eps N := by
  unfold sourceRadialLogOneRunQueryEnvelope
  positivity

/-! ## The actual terminal index, twice -/

/-- The terminal chunk is bounded by the clipped radial logarithm in the form useful for
both occurrences in the cost product. -/
theorem hybrid_terminalChunk_cast_le_three_sourceLog
    {n : Nat} (hn : 1 ≤ n) {N s0 : Real}
    (hN : 1 ≤ N) (hs0 : 0 < s0) (hs01 : s0 ≤ 1) :
    (adaptiveTerminalChunk N (coldEnd n s0) : Real) ≤
      3 * sourceLogFactor N := by
  have h := hybrid_terminalChunk_cast_lt_two_sourceLog_add_one hn hN hs0 hs01
  have hL : 1 ≤ sourceLogFactor N := le_max_left _ _
  linarith

/-- At the literal source start, the cancelled cold/hot proposal core spends its single
copy of the terminal radial logarithm.  `q` is the radius-four mixing coefficient; its
square is kept in the numerical coefficient instead of being confused with a log. -/
theorem sourceHybridCore_terminal_le
    {n : Nat} (hn : 1 ≤ n) {N q : Real} (hN : 1 ≤ N) :
    2 * coldPhases n (1 / (16 * (n : Real))) +
        24 * q ^ 2 * (n : Real) ^ 2 * N *
          adaptiveTerminalChunk N
            (coldEnd n (1 / (16 * (n : Real)))) ≤
      (66 + 72 * q ^ 2) *
        max (N * (n : Real) ^ 2) ((n : Real) ^ 3) *
          sourceLogFactor n * sourceLogFactor N := by
  have hn0 : (0 : Real) < n := by exact_mod_cast Nat.zero_lt_of_lt hn
  have hn1 : (1 : Real) ≤ n := by exact_mod_cast hn
  have hs0 : 0 < (1 / (16 * (n : Real)) : Real) := by positivity
  have hs01 : (1 / (16 * (n : Real)) : Real) ≤ 1 := by
    rw [div_le_one (by positivity : (0 : Real) < 16 * (n : Real))]
    nlinarith
  have hcdiv := coldPhases_source_div_lt_thirtyThree_log hn
  have hc : (coldPhases n (1 / (16 * (n : Real))) : Real) ≤
      33 * (n : Real) * sourceLogFactor n := by
    rw [div_lt_iff₀ hn0] at hcdiv
    nlinarith
  have hJ := hybrid_terminalChunk_cast_le_three_sourceLog hn hN hs0 hs01
  have hLn : 1 ≤ sourceLogFactor n := le_max_left _ _
  have hLN : 1 ≤ sourceLogFactor N := le_max_left _ _
  have hmaxN : N * (n : Real) ^ 2 ≤
      max (N * (n : Real) ^ 2) ((n : Real) ^ 3) := le_max_left _ _
  have hmaxn : (n : Real) ^ 3 ≤
      max (N * (n : Real) ^ 2) ((n : Real) ^ 3) := le_max_right _ _
  have hq0 : 0 ≤ q ^ 2 := sq_nonneg q
  have hmax0 : 0 ≤ max (N * (n : Real) ^ 2) ((n : Real) ^ 3) := by
    exact (by positivity : 0 ≤ (n : Real) ^ 3) |>.trans hmaxn
  have hc' : 2 * (coldPhases n (1 / (16 * (n : Real))) : Real) ≤
      66 * max (N * (n : Real) ^ 2) ((n : Real) ^ 3) *
        sourceLogFactor n * sourceLogFactor N := by
    calc
      _ ≤ 66 * (n : Real) * sourceLogFactor n := by linarith
      _ ≤ 66 * (n : Real) ^ 3 * sourceLogFactor n * sourceLogFactor N := by
        have hn13 : (n : Real) ≤ (n : Real) ^ 3 := by nlinarith
        nlinarith [mul_nonneg (by positivity : 0 ≤ 66 * sourceLogFactor n)
          (sub_nonneg.2 hLN)]
      _ ≤ 66 * max (N * (n : Real) ^ 2) ((n : Real) ^ 3) *
          sourceLogFactor n * sourceLogFactor N := by gcongr
  have hhot : 24 * q ^ 2 * (n : Real) ^ 2 * N *
        (adaptiveTerminalChunk N
          (coldEnd n (1 / (16 * (n : Real)))) : Real) ≤
      72 * q ^ 2 * max (N * (n : Real) ^ 2) ((n : Real) ^ 3) *
        sourceLogFactor n * sourceLogFactor N := by
    calc
      _ ≤ 24 * q ^ 2 * (n : Real) ^ 2 * N *
          (3 * sourceLogFactor N) := by gcongr
      _ = 72 * q ^ 2 * (N * (n : Real) ^ 2) * sourceLogFactor N := by ring
      _ ≤ 72 * q ^ 2 *
          max (N * (n : Real) ^ 2) ((n : Real) ^ 3) *
            sourceLogFactor N := by gcongr
      _ ≤ 72 * q ^ 2 *
          max (N * (n : Real) ^ 2) ((n : Real) ^ 3) *
            sourceLogFactor n * sourceLogFactor N := by
        have hbase : 0 ≤ 72 * q ^ 2 *
            max (N * (n : Real) ^ 2) ((n : Real) ^ 3) *
              sourceLogFactor N := by positivity
        nlinarith [mul_nonneg hbase (sub_nonneg.2 hLn)]
  calc
    _ ≤ 66 * max (N * (n : Real) ^ 2) ((n : Real) ^ 3) *
          sourceLogFactor n * sourceLogFactor N +
        72 * q ^ 2 * max (N * (n : Real) ^ 2) ((n : Real) ^ 3) *
          sourceLogFactor n * sourceLogFactor N := add_le_add hc' hhot
    _ = _ := by ring

/-- Multiplying the two actual terminal-index estimates gives exactly the additional
`sourceLogFactor N ^ 2`, and no additional accuracy denominator. -/
theorem actualTerminal_coldHotCore_le_radialLogCore
    {n : Nat} (hn : 1 ≤ n) {N q overhead eps : Real}
    (hN : 1 ≤ N) (hoverhead0 : 0 ≤ overhead) :
    2 * weightedSampleNumerator n
          (coldPhases n (1 / (16 * (n : Real))))
          (adaptiveTerminalChunk N
            (coldEnd n (1 / (16 * (n : Real))))) * overhead *
        (2 * coldPhases n (1 / (16 * (n : Real))) +
          24 * q ^ 2 * (n : Real) ^ 2 * N *
            adaptiveTerminalChunk N
              (coldEnd n (1 / (16 * (n : Real))))) ≤
      sourceRadialLogOneRunQueryCore
        (2 * 7004 * (66 + 72 * q ^ 2) * overhead)
        n (Real.sqrt N) eps N := by
  have hw := weightedSampleNumerator_source_terminal_le hn hN
  have hh := sourceHybridCore_terminal_le (q := q) hn hN
  have hmax0 : 0 ≤ max (N * (n : Real) ^ 2) ((n : Real) ^ 3) := by positivity
  have hLn0 : 0 ≤ sourceLogFactor n := (sourceLogFactor_pos n).le
  have hLN0 : 0 ≤ sourceLogFactor N := (sourceLogFactor_pos N).le
  have hsqrt : (Real.sqrt N) ^ 2 = N :=
    Real.sq_sqrt (zero_le_one.trans hN)
  unfold sourceRadialLogOneRunQueryCore sourceOneRunQueryCore
  rw [hsqrt]
  calc
    _ ≤ 2 * (7004 * sourceLogFactor n * sourceLogFactor N) * overhead *
        ((66 + 72 * q ^ 2) *
          max (N * (n : Real) ^ 2) ((n : Real) ^ 3) *
            sourceLogFactor n * sourceLogFactor N) := by gcongr
    _ ≤ (2 * 7004 * (66 + 72 * q ^ 2) * overhead) *
        (max (N * (n : Real) ^ 2) ((n : Real) ^ 3) *
          sourceLogFactor n ^ 2 * sourceLogFactor (1 / eps) ^ 2 *
            sourceLogFactor ((n : Real) / eps) ^ 2) *
          sourceLogFactor N ^ 2 := by
      have hLe : 1 ≤ sourceLogFactor (1 / eps) ^ 2 := by
        simpa only [one_pow, sourceLogFactor] using
          pow_le_pow_left₀ zero_le_one
            (le_max_left (1 : Real) (Real.log (1 / eps))) 2
      have hLne : 1 ≤ sourceLogFactor ((n : Real) / eps) ^ 2 := by
        simpa only [one_pow, sourceLogFactor] using
          pow_le_pow_left₀ zero_le_one
            (le_max_left (1 : Real) (Real.log ((n : Real) / eps))) 2
      have hcoef : 0 ≤ 2 * 7004 * (66 + 72 * q ^ 2) * overhead *
          max (N * (n : Real) ^ 2) ((n : Real) ^ 3) *
            sourceLogFactor n ^ 2 * sourceLogFactor N ^ 2 := by positivity
      calc
        _ = (2 * 7004 * (66 + 72 * q ^ 2) * overhead *
            max (N * (n : Real) ^ 2) ((n : Real) ^ 3) *
              sourceLogFactor n ^ 2 * sourceLogFactor N ^ 2) := by ring
        _ ≤ (2 * 7004 * (66 + 72 * q ^ 2) * overhead *
            max (N * (n : Real) ^ 2) ((n : Real) ^ 3) *
              sourceLogFactor n ^ 2 * sourceLogFactor N ^ 2) *
              sourceLogFactor (1 / eps) ^ 2 :=
          le_mul_of_one_le_right hcoef hLe
        _ ≤ (2 * 7004 * (66 + 72 * q ^ 2) * overhead *
            max (N * (n : Real) ^ 2) ((n : Real) ^ 3) *
              sourceLogFactor n ^ 2 * sourceLogFactor N ^ 2) *
              sourceLogFactor (1 / eps) ^ 2 *
                sourceLogFactor ((n : Real) / eps) ^ 2 :=
          le_mul_of_one_le_right (by positivity) hLne
        _ = _ := by ring

/-! ## Public arithmetic contract -/

/-- The honest clipped CV complexity is nonnegative. -/
theorem cvRadialLogComplexityShapeClipped_nonneg
    (n : Nat) (R2 eps p : Real) (hR2 : 0 ≤ R2) :
    0 ≤ cvRadialLogComplexityShapeClipped n R2 eps p := by
  unfold cvRadialLogComplexityShapeClipped
  exact mul_nonneg (cvComplexityShapeClipped_nonneg n R2 eps p hR2)
    (sq_nonneg _)

/-- The amplified honest source envelope fits the public radial-log shape. -/
theorem sourceRadialLogAmplifiedQueryEnvelope_le
    {runtimeConstant radius eps N p R2 : Real} {n : Nat}
    (hconstant : 0 ≤ runtimeConstant) (hn : 1 ≤ n)
    (hR2 : 0 ≤ R2) (hradius : radius ^ 2 ≤ R2)
    (hN : 0 < N) (hNle : N ≤ max 1 R2)
    (heps : 0 < eps) (heps1 : eps < 1)
    (hp : 0 < p) (hp1 : p < 1) :
    sourceRadialLogAmplifiedQueryEnvelope runtimeConstant n radius eps N p ≤
      (200 * (runtimeConstant + 1)) *
        cvRadialLogComplexityShapeClipped n R2 eps p := by
  let B : Real := cvComplexityShapeClipped n R2 eps p /
    max 1 (Real.log (1 / p))
  let Lp : Real := max 1 (Real.log (1 / p))
  let LN : Real := sourceLogFactor N
  let LR : Real := sourceLogFactor (max 1 R2)
  have hbase1 := one_le_cvBaseClipped hn hR2 heps heps1
  have hLp1 : 1 ≤ Lp := le_max_left _ _
  have hLN0 : 0 ≤ LN := (sourceLogFactor_pos N).le
  have hLR1 : 1 ≤ LR := le_max_left _ _
  have hNlog : LN ≤ LR := sourceLogFactor_mono_of_pos hN hNle
  have hlogp : 0 ≤ Real.log (1 / p) := by
    apply Real.log_nonneg
    rw [le_div_iff₀ hp]
    simpa only [one_mul] using hp1.le
  have hfactor : 8 * Real.log (1 / p) + 2 ≤ 10 * Lp := by
    have := le_max_right (1 : Real) (Real.log (1 / p))
    linarith
  have hbase1' : (1 : Real) ≤
      (max (R2 * (n : Real) ^ 2) ((n : Real) ^ 3) / eps ^ 2) *
        sourceLogFactor n ^ 2 * sourceLogFactor (1 / eps) ^ 2 *
          sourceLogFactor ((n : Real) / eps) ^ 2 := by
    simpa only [sourceLogFactor] using hbase1
  have hrun : sourceRadialLogOneRunQueryEnvelope runtimeConstant n radius eps N ≤
      runtimeConstant *
        ((max (R2 * (n : Real) ^ 2) ((n : Real) ^ 3) / eps ^ 2) *
          sourceLogFactor n ^ 2 * sourceLogFactor (1 / eps) ^ 2 *
            sourceLogFactor ((n : Real) / eps) ^ 2) * LR ^ 2 := by
    unfold sourceRadialLogOneRunQueryEnvelope
    have hLR0 : (0 : Real) ≤ LR ^ 2 := by positivity
    calc
      runtimeConstant * sourceLogFactor N ^ 2 = runtimeConstant * LN ^ 2 := rfl
      _ ≤ runtimeConstant * LR ^ 2 := by gcongr
      _ ≤ runtimeConstant *
            ((max (R2 * (n : Real) ^ 2) ((n : Real) ^ 3) / eps ^ 2) *
              sourceLogFactor n ^ 2 * sourceLogFactor (1 / eps) ^ 2 *
                sourceLogFactor ((n : Real) / eps) ^ 2) * LR ^ 2 :=
        mul_le_mul_of_nonneg_right
          (le_mul_of_one_le_right hconstant hbase1') hLR0
  have hmain1 : 1 ≤
      ((max (R2 * (n : Real) ^ 2) ((n : Real) ^ 3) / eps ^ 2) *
        sourceLogFactor n ^ 2 * sourceLogFactor (1 / eps) ^ 2 *
          sourceLogFactor ((n : Real) / eps) ^ 2) * LR ^ 2 := by
    have hbase1' : 1 ≤
        (max (R2 * (n : Real) ^ 2) ((n : Real) ^ 3) / eps ^ 2) *
          sourceLogFactor n ^ 2 * sourceLogFactor (1 / eps) ^ 2 *
            sourceLogFactor ((n : Real) / eps) ^ 2 := by
      simpa only [sourceLogFactor] using hbase1
    calc
      1 ≤ (max (R2 * (n : Real) ^ 2) ((n : Real) ^ 3) / eps ^ 2) *
          sourceLogFactor n ^ 2 * sourceLogFactor (1 / eps) ^ 2 *
            sourceLogFactor ((n : Real) / eps) ^ 2 := hbase1'
      _ ≤ _ := le_mul_of_one_le_right (by positivity) (by nlinarith [hLR1])
  unfold sourceRadialLogAmplifiedQueryEnvelope
  calc
    _ ≤ (10 * Lp) *
        (20 * (sourceRadialLogOneRunQueryEnvelope runtimeConstant n radius eps N + 1)) := by
      exact mul_le_mul_of_nonneg_right hfactor
        (mul_nonneg (by norm_num)
          (add_nonneg
            (sourceRadialLogOneRunQueryEnvelope_nonneg hconstant n radius eps N)
            zero_le_one))
    _ ≤ (10 * Lp) * (20 *
        (runtimeConstant *
          ((max (R2 * (n : Real) ^ 2) ((n : Real) ^ 3) / eps ^ 2) *
            sourceLogFactor n ^ 2 * sourceLogFactor (1 / eps) ^ 2 *
              sourceLogFactor ((n : Real) / eps) ^ 2) * LR ^ 2 + 1)) := by gcongr
    _ ≤ (10 * Lp) * (20 *
        ((runtimeConstant + 1) *
          ((max (R2 * (n : Real) ^ 2) ((n : Real) ^ 3) / eps ^ 2) *
            sourceLogFactor n ^ 2 * sourceLogFactor (1 / eps) ^ 2 *
              sourceLogFactor ((n : Real) / eps) ^ 2) * LR ^ 2)) := by
          gcongr
          nlinarith
    _ = (200 * (runtimeConstant + 1)) *
        cvRadialLogComplexityShapeClipped n R2 eps p := by
      unfold cvRadialLogComplexityShapeClipped cvComplexityShapeClipped
      dsimp only [Lp, LR]
      simp only [sourceLogFactor]
      ring

/-! ## A genuine public stopped-cost oracle for the radial-log budget -/

/-- Re-express the radial factor as an input-local effective source constant.  This lets
us reuse the already machine-checked cutoff and median implementation without copying its
probability proof. -/
noncomputable def radialLogEffectiveRuntime
    (runtimeConstant N : Real) : Real :=
  runtimeConstant * sourceLogFactor N ^ 2

theorem sourceOneRunQueryEnvelope_effective_eq_radialLog
    (runtimeConstant : Real) (n : Nat) (radius eps N : Real) :
    sourceOneRunQueryEnvelope (radialLogEffectiveRuntime runtimeConstant N)
        n radius eps =
      sourceRadialLogOneRunQueryEnvelope runtimeConstant n radius eps N := by
  unfold radialLogEffectiveRuntime sourceOneRunQueryEnvelope
    sourceRadialLogOneRunQueryEnvelope
  ring

theorem sourceOneRunQueryBudget_effective_eq_radialLog
    (runtimeConstant : Real) (n : Nat) (radius eps N : Real) :
    sourceOneRunQueryBudget (radialLogEffectiveRuntime runtimeConstant N)
        n radius eps =
      sourceRadialLogOneRunQueryBudget runtimeConstant n radius eps N := by
  unfold sourceOneRunQueryBudget sourceRadialLogOneRunQueryBudget
  rw [sourceOneRunQueryEnvelope_effective_eq_radialLog]

theorem sourceAmplifiedQueryEnvelope_effective_eq_radialLog
    (runtimeConstant : Real) (n : Nat) (radius eps N p : Real) :
    sourceAmplifiedQueryEnvelope (radialLogEffectiveRuntime runtimeConstant N)
        n radius eps p =
      sourceRadialLogAmplifiedQueryEnvelope runtimeConstant n radius eps N p := by
  unfold sourceAmplifiedQueryEnvelope sourceRadialLogAmplifiedQueryEnvelope
  rw [sourceOneRunQueryEnvelope_effective_eq_radialLog]

/-- Input-indexed concrete one-run certificates with the honest radial-log mean budget. -/
structure RadialLogSourcePublicOneRunCertificates
    (n : Nat) (runtimeConstant : Real)
    (radialR radialN : Set (Ttc.Space n) → Real)
    (Omega : Ttc.CVAdaptive.VolumeInput n → Type)
    [∀ a, MeasurableSpace (Omega a)]
    (oneLaw : ∀ a, Measure (Omega a))
    (cost : ∀ a, Omega a → ENNReal)
    (value : ∀ a, Omega a → Real) : Prop where
  probability : ∀ a, IsProbabilityMeasure (oneLaw a)
  cost_measurable : ∀ a, Measurable (cost a)
  value_measurable : ∀ a, Measurable (value a)
  expected_queries : ∀ a,
    (∫⁻ omega, cost a omega ∂oneLaw a) ≤
      sourceRadialLogOneRunQueryBudget runtimeConstant n
        (radialR a.1) a.2.1 (radialN a.1)
  accuracy : ∀ (K : Set (Ttc.Space n)) (eps p : Real),
    0 < eps → 0 < p → p < 1 → Convex Real K →
    Metric.ball (0 : Ttc.Space n) 1 ⊆ K → volume K ≠ ⊤ →
    4 / 5 ≤ (oneLaw (K, eps, p)).real
      {omega | value (K, eps, p) omega ∈
        Icc ((1 - eps) * (volume K).toReal) ((1 + eps) * (volume K).toReal)}

/-- Exact public expected bound used by the radial-log stopped oracle. -/
noncomputable def radialLogSourcePublicExpectedBound
    (runtimeConstant : Real) (n : Nat)
    (radialR radialN : Set (Ttc.Space n) → Real)
    (K : Set (Ttc.Space n)) (eps p : Real) : ENNReal :=
  sourceOuterCutoffBudget
    (radialLogEffectiveRuntime runtimeConstant (radialN K)) n
    (outerCutoffReps p) (radialR K) eps

/-- Public expected-query volume oracle with the actual stopped cost on its coin space.
The only conditional input is the concrete one-run law/cost/output certificate. -/
noncomputable def expectedQueryVolumeAlgorithmOfRadialLogSourceCertificates
    (n : Nat) (runtimeConstant : Real)
    (radialR radialN : Set (Ttc.Space n) → Real)
    (Omega : Ttc.CVAdaptive.VolumeInput n → Type)
    [mOmega : ∀ a, MeasurableSpace (Omega a)]
    (oneLaw : ∀ a, Measure (Omega a))
    (cost : ∀ a, Omega a → ENNReal)
    (value : ∀ a, Omega a → Real)
    (hcert : RadialLogSourcePublicOneRunCertificates n runtimeConstant
      radialR radialN Omega oneLaw cost value) :
    Ttc.ExpectedQueryVolumeAlgorithm n := by
  let effective : Ttc.CVAdaptive.VolumeInput n → Real := fun a =>
    radialLogEffectiveRuntime runtimeConstant (radialN a.1)
  let X : Ttc.CVAdaptive.VolumeInput n → Type := fun a =>
    SourceOuterCoin (outerCutoffReps a.2.2) (Omega a)
  letI : ∀ a, MeasurableSpace (X a) := fun _ => inferInstance
  let nu : ∀ a, Measure (X a) := fun a =>
    sourceOuterLaw (oneLaw a) (outerCutoffReps a.2.2)
  let localEst : ∀ a, X a → Real := fun a =>
    sourceOuterEstimator (effective a) n (radialR a.1) a.2.1 0
      (cost a) (value a)
  let localCost : ∀ a, X a → ENNReal := fun a =>
    sourceOuterQueryCost (effective a) n (radialR a.1) a.2.1 (cost a)
  let bound : Ttc.CVAdaptive.VolumeInput n → ENNReal := fun a =>
    radialLogSourcePublicExpectedBound runtimeConstant n radialR radialN
      a.1 a.2.1 a.2.2
  letI : ∀ a, IsProbabilityMeasure (oneLaw a) := hcert.probability
  letI : ∀ a, IsProbabilityMeasure (nu a) := by
    intro a
    dsimp only [nu, X, sourceOuterLaw]
    infer_instance
  apply Ttc.ExpectedQueryVolumeAlgorithm.ofInputCostedLaws n X nu localEst localCost
    (bound := bound)
  · intro a
    dsimp only [localEst, X]
    apply measurable_medianSel
    intro i
    exact (measurable_cutoffValue (hcert.cost_measurable a)
      (hcert.value_measurable a)).comp (measurable_pi_apply i)
  · intro a
    dsimp only [localCost, X]
    exact measurable_sourceOuterQueryCost (hcert.cost_measurable a)
  · intro a
    dsimp only [localCost, nu, X, bound, radialLogSourcePublicExpectedBound,
      effective]
    exact sourceOuter_expectedQueryCost_le (oneLaw a)
  · intro K eps p heps hp hp1 hKc hball hfin
    let a : Ttc.CVAdaptive.VolumeInput n := (K, eps, p)
    let cert : SourceOneRunCertificate (oneLaw a) (cost a) (value a)
        (radialLogEffectiveRuntime runtimeConstant (radialN K)) n
        (radialR K) eps
        ((1 - eps) * (volume K).toReal) ((1 + eps) * (volume K).toReal) :=
      { probability := hcert.probability a
        cost_measurable := hcert.cost_measurable a
        value_measurable := hcert.value_measurable a
        expected_queries := by
          rw [sourceOneRunQueryBudget_effective_eq_radialLog]
          exact hcert.expected_queries a
        accuracy := hcert.accuracy K eps p heps hp hp1 hKc hball hfin }
    dsimp only [nu, localEst, X, effective]
    exact source_median_cutoff_accuracy (oneLaw a) (cost a) (value a) cert hp

theorem radialLogSourcePublicExpectedBound_le_amplified
    {runtimeConstant : Real} (hconstant : 0 ≤ runtimeConstant) {n : Nat}
    (radialR radialN : Set (Ttc.Space n) → Real) (K : Set (Ttc.Space n))
    {eps p : Real} (hp : 0 < p) (hp1 : p < 1) :
    radialLogSourcePublicExpectedBound runtimeConstant n radialR radialN K eps p ≤
      ENNReal.ofReal (sourceRadialLogAmplifiedQueryEnvelope runtimeConstant n
        (radialR K) eps (radialN K) p) := by
  unfold radialLogSourcePublicExpectedBound
  rw [← sourceAmplifiedQueryEnvelope_effective_eq_radialLog]
  apply sourceOuterCutoffBudget_le_explicit
  · unfold radialLogEffectiveRuntime
    positivity
  · exact hp
  · exact hp1

/-! The retained-history construction supplies reference-TV one-run certificates, so the
public radial-log oracle needs the matching stopped-reference variant as well. -/

structure RadialLogSourcePublicReferenceTVCertificates
    (n : Nat) (runtimeConstant : Real)
    (radialR radialN : Set (Ttc.Space n) → Real)
    (Omega : Ttc.CVAdaptive.VolumeInput n → Type)
    [∀ a, MeasurableSpace (Omega a)]
    (actual reference : ∀ a, Measure (Omega a))
    (cost : ∀ a, Omega a → ENNReal)
    (value : ∀ a, Omega a → Real) : Prop where
  actual_probability : ∀ a, IsProbabilityMeasure (actual a)
  reference_probability : ∀ a, IsProbabilityMeasure (reference a)
  cost_measurable : ∀ a, Measurable (cost a)
  value_measurable : ∀ a, Measurable (value a)
  path_tv : ∀ a, TVLe
    (actual a) (reference a) (ENNReal.ofReal (1 / 40 : Real))
  reference_expected_queries : ∀ a,
    (∫⁻ omega, cost a omega ∂reference a) ≤
      sourceRadialLogOneRunQueryBudget runtimeConstant n
        (radialR a.1) a.2.1 (radialN a.1)
  accuracy : ∀ (K : Set (Ttc.Space n)) (eps p : Real),
    0 < eps → 0 < p → p < 1 → Convex Real K →
    Metric.ball (0 : Ttc.Space n) 1 ⊆ K → volume K ≠ ⊤ →
    4 / 5 ≤ (actual (K, eps, p)).real
      {omega | value (K, eps, p) omega ∈
        Icc ((1 - eps) * (volume K).toReal) ((1 + eps) * (volume K).toReal)}

noncomputable def radialLogSourceReferencePublicExpectedBound
    (runtimeConstant : Real) (n : Nat)
    (radialR radialN : Set (Ttc.Space n) → Real)
    (K : Set (Ttc.Space n)) (eps p : Real) : ENNReal :=
  Ttc.CVSourceReferenceTVCapstone.sourceReferencePublicExpectedBound
    (radialLogEffectiveRuntime runtimeConstant (radialN K)) n radialR K eps p

/-- Public stopped actual-law oracle built from input-indexed radial-log reference-TV
certificates.  Thus the concrete retained-history route can consume the honest envelope
without first proving a generally false actual-law mean bound. -/
noncomputable def expectedQueryVolumeAlgorithmOfRadialLogSourceReferenceTVCertificates
    (n : Nat) (runtimeConstant : Real)
    (radialR radialN : Set (Ttc.Space n) → Real)
    (Omega : Ttc.CVAdaptive.VolumeInput n → Type)
    [mOmega : ∀ a, MeasurableSpace (Omega a)]
    (actual reference : ∀ a, Measure (Omega a))
    (cost : ∀ a, Omega a → ENNReal)
    (value : ∀ a, Omega a → Real)
    (hcert : RadialLogSourcePublicReferenceTVCertificates n runtimeConstant
      radialR radialN Omega actual reference cost value) :
    Ttc.ExpectedQueryVolumeAlgorithm n := by
  let effective : Ttc.CVAdaptive.VolumeInput n → Real := fun a =>
    radialLogEffectiveRuntime runtimeConstant (radialN a.1)
  let X : Ttc.CVAdaptive.VolumeInput n → Type := fun a =>
    Ttc.CVSourceReferenceTVCapstone.SourceReferenceOuterCoin
      (outerCutoffReps a.2.2) (Omega a)
  letI : ∀ a, MeasurableSpace (X a) := fun _ => inferInstance
  let nu : ∀ a, Measure (X a) := fun a =>
    sourceOuterLaw (actual a) (outerCutoffReps a.2.2)
  let localEst : ∀ a, X a → Real := fun a =>
    Ttc.CVSourceReferenceTVCapstone.sourceReferenceOuterEstimator
      (effective a) n (radialR a.1) a.2.1 0 (cost a) (value a)
  let localCost : ∀ a, X a → ENNReal := fun a =>
    Ttc.CVSourceReferenceTVCapstone.sourceReferenceOuterQueryCost
      (effective a) n (radialR a.1) a.2.1 (cost a)
  let bound : Ttc.CVAdaptive.VolumeInput n → ENNReal := fun a =>
    radialLogSourceReferencePublicExpectedBound runtimeConstant n radialR radialN
      a.1 a.2.1 a.2.2
  letI : ∀ a, IsProbabilityMeasure (actual a) := hcert.actual_probability
  letI : ∀ a, IsProbabilityMeasure (reference a) := hcert.reference_probability
  letI : ∀ a, IsProbabilityMeasure (nu a) := by
    intro a
    dsimp only [nu, X, sourceOuterLaw]
    infer_instance
  apply Ttc.ExpectedQueryVolumeAlgorithm.ofInputCostedLaws n X nu localEst localCost
    (bound := bound)
  · intro a
    dsimp only [localEst, X]
    apply measurable_medianSel
    intro i
    exact (measurable_cutoffValue (hcert.cost_measurable a)
      (hcert.value_measurable a)).comp (measurable_pi_apply i)
  · intro a
    dsimp only [localCost, X]
    exact Ttc.CVSourceReferenceTVCapstone.measurable_sourceReferenceOuterQueryCost
      (hcert.cost_measurable a)
  · intro a
    dsimp only [localCost, nu, X, bound,
      radialLogSourceReferencePublicExpectedBound, effective]
    exact Ttc.CVSourceReferenceTVCapstone.sourceReferenceOuter_expectedQueryCost_le
      (actual a)
  · intro K eps p heps hp hp1 hKc hball hfin
    let a : Ttc.CVAdaptive.VolumeInput n := (K, eps, p)
    let cert : Ttc.CVSourceReferenceTVCapstone.SourceReferenceTVOneRunCertificate
        (actual a) (reference a) (cost a) (value a)
        (radialLogEffectiveRuntime runtimeConstant (radialN K)) n
        (radialR K) eps
        ((1 - eps) * (volume K).toReal) ((1 + eps) * (volume K).toReal) :=
      { actual_probability := hcert.actual_probability a
        reference_probability := hcert.reference_probability a
        cost_measurable := hcert.cost_measurable a
        value_measurable := hcert.value_measurable a
        path_tv := hcert.path_tv a
        reference_expected_queries := by
          rw [sourceOneRunQueryBudget_effective_eq_radialLog]
          exact hcert.reference_expected_queries a
        accuracy := hcert.accuracy K eps p heps hp hp1 hKc hball hfin }
    dsimp only [nu, localEst, X, effective]
    exact Ttc.CVSourceReferenceTVCapstone.sourceReference_median_cutoff_accuracy
      (actual a) (reference a) (cost a) (value a) cert hp

theorem radialLogSourceReferencePublicExpectedBound_le_two_amplified
    {runtimeConstant : Real} (hconstant : 0 ≤ runtimeConstant) {n : Nat}
    (radialR radialN : Set (Ttc.Space n) → Real) (K : Set (Ttc.Space n))
    {eps p : Real} (hp : 0 < p) (hp1 : p < 1) :
    radialLogSourceReferencePublicExpectedBound runtimeConstant n
        radialR radialN K eps p ≤
      2 * ENNReal.ofReal (sourceRadialLogAmplifiedQueryEnvelope runtimeConstant n
        (radialR K) eps (radialN K) p) := by
  unfold radialLogSourceReferencePublicExpectedBound
  rw [Ttc.CVSourceReferenceTheorem11Arithmetic.sourceReferencePublicExpectedBound_eq_two_mul]
  gcongr
  rw [← sourceAmplifiedQueryEnvelope_effective_eq_radialLog]
  exact sourcePublicExpectedBound_le_polynomial (by
    unfold radialLogEffectiveRuntime
    positivity) radialR K hp hp1

theorem radialLogSourceReferenceExpectedAlgorithm_expectedBound_le_shape
    {n : Nat} {runtimeConstant : Real} (hconstant : 0 ≤ runtimeConstant)
    (radialR radialN : Set (Ttc.Space n) → Real)
    (Omega : Ttc.CVAdaptive.VolumeInput n → Type)
    [∀ a, MeasurableSpace (Omega a)]
    (actual reference : ∀ a, Measure (Omega a))
    (cost : ∀ a, Omega a → ENNReal) (value : ∀ a, Omega a → Real)
    (hcert : RadialLogSourcePublicReferenceTVCertificates n runtimeConstant
      radialR radialN Omega actual reference cost value)
    {K : Set (Ttc.Space n)} {R2 eps p : Real}
    (hn : 1 ≤ n) (heps : 0 < eps) (heps1 : eps < 1)
    (hp : 0 < p) (hp1 : p < 1) (hK : CVAdmissible K R2)
    (hrad : (radialR K) ^ 2 ≤ R2) (hNpos : 0 < radialN K)
    (hNle : radialN K ≤ max 1 R2) :
    (expectedQueryVolumeAlgorithmOfRadialLogSourceReferenceTVCertificates n
      runtimeConstant radialR radialN Omega actual reference cost value hcert).expectedBound
        K eps p ≤ ENNReal.ofReal
          ((400 * (runtimeConstant + 1)) *
            cvRadialLogComplexityShapeClipped n R2 eps p) := by
  have hR20 : 0 ≤ R2 := by
    have hm0 : 0 ≤ cvSecondMoment K := by
      unfold cvSecondMoment
      exact integral_nonneg (fun _ ↦ sq_nonneg _)
    exact hm0.trans hK.2.2.2.2
  change radialLogSourceReferencePublicExpectedBound runtimeConstant n
    radialR radialN K eps p ≤ _
  calc
    _ ≤ 2 * ENNReal.ofReal
        (sourceRadialLogAmplifiedQueryEnvelope runtimeConstant n
          (radialR K) eps (radialN K) p) :=
      radialLogSourceReferencePublicExpectedBound_le_two_amplified
        hconstant radialR radialN K hp hp1
    _ ≤ 2 * ENNReal.ofReal
        ((200 * (runtimeConstant + 1)) *
          cvRadialLogComplexityShapeClipped n R2 eps p) := by
      gcongr
      exact sourceRadialLogAmplifiedQueryEnvelope_le hconstant hn hR20
        hrad hNpos hNle heps heps1 hp hp1
    _ = ENNReal.ofReal
        ((400 * (runtimeConstant + 1)) *
          cvRadialLogComplexityShapeClipped n R2 eps p) := by
      rw [← ENNReal.ofReal_ofNat 2,
        ← ENNReal.ofReal_mul (by norm_num : (0 : Real) ≤ 2)]
      congr 1
      ring

/-- Honest public expected-query variant of CV Theorem 1.1 for the literal hybrid
schedule. -/
structure CVRadialLogExpectedImplementation where
  algorithm : (n : Nat) → Ttc.ExpectedQueryVolumeAlgorithm n
  runtimeConstant : Real
  runtimeConstant_nonneg : 0 ≤ runtimeConstant
  expectedBound_le : ∀ (n : Nat) (K : Set (Ttc.Space n)) (eps p R2 : Real),
    1 ≤ n → 0 < eps → eps < 1 → 0 < p → p < 1 → CVAdmissible K R2 →
    (algorithm n).expectedBound K eps p ≤ ENNReal.ofReal
      (runtimeConstant * cvRadialLogComplexityShapeClipped n R2 eps p)

/-- Arithmetic constructor from a public algorithm bounded by the amplified honest
source envelope.  Execution/accuracy stays in `ExpectedQueryVolumeAlgorithm`; this
constructor discharges all confidence and public-shape arithmetic. -/
noncomputable def cvRadialLogExpectedImplementationOfSourceFamily
    (runtimeConstant : Real) (hconstant : 0 ≤ runtimeConstant)
    (algorithm : (n : Nat) → Ttc.ExpectedQueryVolumeAlgorithm n)
    (radialR radialN : ∀ n, Set (Ttc.Space n) → Real)
    (hsource : ∀ n (K : Set (Ttc.Space n)) eps p,
      0 < eps → eps < 1 → 0 < p → p < 1 →
      (algorithm n).expectedBound K eps p ≤ ENNReal.ofReal
        (sourceRadialLogAmplifiedQueryEnvelope runtimeConstant n
          (radialR n K) eps (radialN n K) p))
    (hrad : ∀ n (K : Set (Ttc.Space n)) R2,
      CVAdmissible K R2 → (radialR n K) ^ 2 ≤ R2)
    (hNpos : ∀ n (K : Set (Ttc.Space n)), 0 < radialN n K)
    (hNle : ∀ n (K : Set (Ttc.Space n)) R2,
      CVAdmissible K R2 → radialN n K ≤ max 1 R2) :
    CVRadialLogExpectedImplementation where
  algorithm := algorithm
  runtimeConstant := 200 * (runtimeConstant + 1)
  runtimeConstant_nonneg := by positivity
  expectedBound_le n K eps p R2 hn heps heps1 hp hp1 hK := by
    have hR20 : 0 ≤ R2 := by
      have hm0 : 0 ≤ cvSecondMoment K := by
        unfold cvSecondMoment
        exact integral_nonneg (fun _ ↦ sq_nonneg _)
      exact hm0.trans hK.2.2.2.2
    calc
      (algorithm n).expectedBound K eps p ≤ ENNReal.ofReal
          (sourceRadialLogAmplifiedQueryEnvelope runtimeConstant n
            (radialR n K) eps (radialN n K) p) :=
        hsource n K eps p heps heps1 hp hp1
      _ ≤ ENNReal.ofReal
          ((200 * (runtimeConstant + 1)) *
            cvRadialLogComplexityShapeClipped n R2 eps p) :=
        ENNReal.ofReal_le_ofReal
          (sourceRadialLogAmplifiedQueryEnvelope_le hconstant hn hR20
            (hrad n K R2 hK) (hNpos n K) (hNle n K R2 hK)
            heps heps1 hp hp1)

/-- Full public constructor from operational one-run radial-log certificates. -/
noncomputable def cvRadialLogExpectedImplementationOfPublicCertificates
    (runtimeConstant : Real) (hconstant : 0 ≤ runtimeConstant)
    (radialR radialN : ∀ n, Set (Ttc.Space n) → Real)
    (Omega : ∀ n, Ttc.CVAdaptive.VolumeInput n → Type)
    [mOmega : ∀ n a, MeasurableSpace (Omega n a)]
    (oneLaw : ∀ n a, Measure (Omega n a))
    (cost : ∀ n a, Omega n a → ENNReal)
    (value : ∀ n a, Omega n a → Real)
    (hcert : ∀ n, RadialLogSourcePublicOneRunCertificates n runtimeConstant
      (radialR n) (radialN n) (Omega n) (oneLaw n) (cost n) (value n))
    (hrad : ∀ n (K : Set (Ttc.Space n)) R2,
      CVAdmissible K R2 → (radialR n K) ^ 2 ≤ R2)
    (hNpos : ∀ n (K : Set (Ttc.Space n)), 0 < radialN n K)
    (hNle : ∀ n (K : Set (Ttc.Space n)) R2,
      CVAdmissible K R2 → radialN n K ≤ max 1 R2) :
    CVRadialLogExpectedImplementation :=
  cvRadialLogExpectedImplementationOfSourceFamily runtimeConstant hconstant
    (fun n ↦ expectedQueryVolumeAlgorithmOfRadialLogSourceCertificates n
      runtimeConstant (radialR n) (radialN n) (Omega n) (oneLaw n)
        (cost n) (value n) (hcert n)) radialR radialN
    (by
      intro n K eps p _heps _heps1 hp hp1
      change radialLogSourcePublicExpectedBound runtimeConstant n
        (radialR n) (radialN n) K eps p ≤ _
      exact radialLogSourcePublicExpectedBound_le_amplified hconstant
        (radialR n) (radialN n) K hp hp1)
    hrad hNpos hNle

/-- Full public constructor for the retained-history reference-TV route.  This is the
constructor consumed by concrete cold/hot certificates: it executes the actual law,
charges its stopped cost, and uses the reference law only for the timeout estimate. -/
noncomputable def cvRadialLogExpectedImplementationOfReferenceTVFamily
    (runtimeConstant : Real) (hconstant : 0 ≤ runtimeConstant)
    (radialR radialN : ∀ n, Set (Ttc.Space n) → Real)
    (Omega : ∀ n, Ttc.CVAdaptive.VolumeInput n → Type)
    [mOmega : ∀ n a, MeasurableSpace (Omega n a)]
    (actual reference : ∀ n a, Measure (Omega n a))
    (cost : ∀ n a, Omega n a → ENNReal)
    (value : ∀ n a, Omega n a → Real)
    (hcert : ∀ n, RadialLogSourcePublicReferenceTVCertificates n runtimeConstant
      (radialR n) (radialN n) (Omega n) (actual n) (reference n)
        (cost n) (value n))
    (hrad : ∀ n (K : Set (Ttc.Space n)) R2,
      CVAdmissible K R2 → (radialR n K) ^ 2 ≤ R2)
    (hNpos : ∀ n (K : Set (Ttc.Space n)), 0 < radialN n K)
    (hNle : ∀ n (K : Set (Ttc.Space n)) R2,
      CVAdmissible K R2 → radialN n K ≤ max 1 R2) :
    CVRadialLogExpectedImplementation where
  algorithm n :=
    expectedQueryVolumeAlgorithmOfRadialLogSourceReferenceTVCertificates n
      runtimeConstant (radialR n) (radialN n) (Omega n)
        (actual n) (reference n) (cost n) (value n) (hcert n)
  runtimeConstant := 400 * (runtimeConstant + 1)
  runtimeConstant_nonneg := by positivity
  expectedBound_le n K eps p R2 hn heps heps1 hp hp1 hK := by
    have hR20 : 0 ≤ R2 := by
      have hm0 : 0 ≤ cvSecondMoment K := by
        unfold cvSecondMoment
        exact integral_nonneg (fun _ ↦ sq_nonneg _)
      exact hm0.trans hK.2.2.2.2
    change radialLogSourceReferencePublicExpectedBound runtimeConstant n
      (radialR n) (radialN n) K eps p ≤ _
    calc
      _ ≤ 2 * ENNReal.ofReal
          (sourceRadialLogAmplifiedQueryEnvelope runtimeConstant n
            (radialR n K) eps (radialN n K) p) :=
        radialLogSourceReferencePublicExpectedBound_le_two_amplified
          hconstant (radialR n) (radialN n) K hp hp1
      _ ≤ 2 * ENNReal.ofReal
          ((200 * (runtimeConstant + 1)) *
            cvRadialLogComplexityShapeClipped n R2 eps p) := by
        gcongr
        exact sourceRadialLogAmplifiedQueryEnvelope_le hconstant hn hR20
          (hrad n K R2 hK) (hNpos n K) (hNle n K R2 hK)
          heps heps1 hp hp1
      _ = ENNReal.ofReal
          ((400 * (runtimeConstant + 1)) *
            cvRadialLogComplexityShapeClipped n R2 eps p) := by
        rw [← ENNReal.ofReal_ofNat 2,
          ← ENNReal.ofReal_mul (by norm_num : (0 : Real) ≤ 2)]
        congr 1
        ring

/-- Reference-TV radial-log execution above dimension one, with the exact zero-cost
semantic oracle in dimensions zero and one. -/
noncomputable def radialLogReferenceAlgorithmWithExactLowDimensions
    (runtimeConstant : Real)
    (radialR radialN : ∀ n, Set (Ttc.Space n) → Real)
    (Omega : ∀ n, Ttc.CVAdaptive.VolumeInput n → Type)
    [mOmega : ∀ n a, MeasurableSpace (Omega n a)]
    (actual reference : ∀ n a, Measure (Omega n a))
    (cost : ∀ n a, Omega n a → ENNReal)
    (value : ∀ n a, Omega n a → Real)
    (hcert : ∀ n, 2 ≤ n → RadialLogSourcePublicReferenceTVCertificates n
      runtimeConstant (radialR n) (radialN n) (Omega n)
        (actual n) (reference n) (cost n) (value n))
    (n : Nat) : Ttc.ExpectedQueryVolumeAlgorithm n :=
  if hn : 2 ≤ n then
    expectedQueryVolumeAlgorithmOfRadialLogSourceReferenceTVCertificates n
      runtimeConstant (radialR n) (radialN n) (Omega n)
        (actual n) (reference n) (cost n) (value n) (hcert n hn)
  else Ttc.ExpectedQueryVolumeAlgorithm.exactExpected n

/-- Dimension-total radial-log CV certificate from concrete reference-TV certificates
required only in the substantive Gaussian range `n ≥ 2`. -/
noncomputable def cvRadialLogExpectedImplementationOfReferenceTVFamilyDimTwo
    (runtimeConstant : Real) (hconstant : 0 ≤ runtimeConstant)
    (radialR radialN : ∀ n, Set (Ttc.Space n) → Real)
    (Omega : ∀ n, Ttc.CVAdaptive.VolumeInput n → Type)
    [mOmega : ∀ n a, MeasurableSpace (Omega n a)]
    (actual reference : ∀ n a, Measure (Omega n a))
    (cost : ∀ n a, Omega n a → ENNReal)
    (value : ∀ n a, Omega n a → Real)
    (hcert : ∀ n, 2 ≤ n → RadialLogSourcePublicReferenceTVCertificates n
      runtimeConstant (radialR n) (radialN n) (Omega n)
        (actual n) (reference n) (cost n) (value n))
    (hrad : ∀ n, 2 ≤ n → ∀ (K : Set (Ttc.Space n)) R2,
      CVAdmissible K R2 → (radialR n K) ^ 2 ≤ R2)
    (hNpos : ∀ n, 2 ≤ n → ∀ K, 0 < radialN n K)
    (hNle : ∀ n, 2 ≤ n → ∀ (K : Set (Ttc.Space n)) R2,
      CVAdmissible K R2 → radialN n K ≤ max 1 R2) :
    CVRadialLogExpectedImplementation where
  algorithm n := radialLogReferenceAlgorithmWithExactLowDimensions runtimeConstant
    radialR radialN Omega actual reference cost value hcert n
  runtimeConstant := 400 * (runtimeConstant + 1)
  runtimeConstant_nonneg := by positivity
  expectedBound_le n K eps p R2 hn heps heps1 hp hp1 hK := by
    by_cases hn2 : 2 ≤ n
    · rw [radialLogReferenceAlgorithmWithExactLowDimensions, dif_pos hn2]
      exact radialLogSourceReferenceExpectedAlgorithm_expectedBound_le_shape
        hconstant (radialR n) (radialN n) (Omega n) (actual n) (reference n)
          (cost n) (value n) (hcert n hn2) hn heps heps1 hp hp1 hK
          (hrad n hn2 K R2 hK) (hNpos n hn2 K) (hNle n hn2 K R2 hK)
    · rw [radialLogReferenceAlgorithmWithExactLowDimensions, dif_neg hn2]
      simp

#print axioms sourceHybridCore_terminal_le
#print axioms actualTerminal_coldHotCore_le_radialLogCore
#print axioms sourceRadialLogAmplifiedQueryEnvelope_le
#print axioms cvRadialLogExpectedImplementationOfSourceFamily
#print axioms expectedQueryVolumeAlgorithmOfRadialLogSourceCertificates
#print axioms expectedQueryVolumeAlgorithmOfRadialLogSourceReferenceTVCertificates
#print axioms cvRadialLogExpectedImplementationOfReferenceTVFamily
#print axioms cvRadialLogExpectedImplementationOfReferenceTVFamilyDimTwo

end Ttc.CVRadialLogEnvelope

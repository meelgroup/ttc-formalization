import Ttc.Exec.CVSharpScoreTransport
import Ttc.Exec.CVSlowCanonicalMomentBinders

/-!
# The sharp score-transport bound carried through the factor-seven phase-moment layer

`Ttc.CVSharpScoreTransport` proved the sharp interior phase-ratio bound on the slow
schedule,

`coolRatio m (slowSourceSigmaSq n s0) i x ≤ exp (R^2 / (2 σ_i (n+1)))`  (`i + 1 < m`),

together with the terminal statement `coolRatio ≤ exp (1/2)` (valid when `R^2 ≤ σ_i`),
and defined the sharpened transport bound
`phaseScoreTransportBoundSqSharp n R σ i = exp (R^2/(2 σ_i (n+1)))^2 * 15`.  It stopped
at an unused comparison: the factor-seven phase-moment layer
(`Ttc.CVSlowCanonicalPhaseMomentPackage.operational_slowCanonical_positiveScalar_factorSeven_upto`)
hard-codes the loose sup `exp (R^2/(2 σ_i))`.

This file carries the sharp bound through that layer.  Three things had to be sorted out.

**The sup is genuinely piecewise.**  `sharpPhaseSup n R σ m i` is the sharp interior value
at every interior index and the loose value at the terminal index `i + 1 = m` — where the
loose bound *is* the true sup (`Arlib.GaussianCooling.coolRatio_of_last`), so nothing can
be gained there.  `phaseScore_le_sharpPhaseSup` proves the sup bound at every index with
no extra hypothesis; `phaseScore_sharp_le` is the display form the terminal hypothesis
`R^2 ≤ σ_i` buys, namely `exp (R^2/(2 σ_i (n+1))) ⊔ exp (1/2)`.

**The terminal index costs exactly one constant.**  The moment transport consumes the sup
as a *value*: `sq_moment_le_of_tvLe` needs `ε · B^2 · (1 + 2T) ≤ s · ratio^2` with the same
`B` that bounds the score, so any usable `boundSq` must satisfy `boundSq ≥ sup^2 · 15`.
At the terminal index `sup^2 · 15` is the loose `phaseScoreTransportBoundSqSeven` itself, so
**no `boundSq` strictly below the seven bound can be used at that one index**.  The
sharpened `phaseScoreTransportBoundSqSharp` is nevertheless usable at *every* index, because
`R^2 ≤ σ_i` at the terminal index gives `sup^2 ≤ exp 1 < 3` while
`phaseScoreTransportBoundSqSharp ≥ 15`, so `sup^2 · 15 ≤ 3 · boundSqSharp` uniformly
(`sharpPhaseSup_sq_mul_le_three_mul`).  The price is that the mixing-slack binder is taken
at `phaseMomentSlackSeven … / 6` instead of `… / 2`.  That is the **only** difference
between the sharp package below and the original, and by the paragraph above it is forced.

**The tail half is unchanged.**  The radial tail never routes through `boundSq`, and the
sharp tail budget `b * (sharpPhaseSup … * 15) ≤ slack / 2` is *weaker* than the original
one, so `Ttc.CVSlowCanonicalUniformParameters.slowUniformMeanTailFloor` discharges it
verbatim (`slowSharp_htailBudget`).

Nothing in the development is edited or weakened: every statement here is new, and
`sharpPhaseSup_le_loose` / `phaseScoreTransportBoundSqSharp_le_seven` are the explicit
records that the sharpened quantities are below the ones currently in use.
-/

set_option autoImplicit false
set_option maxHeartbeats 4000000

namespace Ttc.CVSharpFactorSeven

open MeasureTheory ProbabilityTheory Metric Set
open Arlib Arlib.Probability Arlib.MarkovChains Arlib.GaussianCooling
open Ttc.CVCorrected Ttc.CVCorrectedRuntime
open Ttc.CVIndependentStreamDependence Ttc.CVScoreSeedPhaseKernel
open Ttc.CVGaussianScoreAwareParameters Ttc.CVGaussianFactorSevenAssembly
open Ttc.CVGaussianWarmFallbackScoreMoment
open Ttc.CVGaussianBlockRetryParameters
open Ttc.CVSlowFullBodySourceSchedule Ttc.CVSlowSourceReferenceCertificate
open Ttc.CVSlowSourceTargetTVAccuracy Ttc.CVRAwareGlobalRadius
open Ttc.CVSlowCanonicalShareBounds Ttc.CVMinimalScoreAwareWarmLogArithmetic
open Ttc.CVSlowCanonicalUniformParameters
open Ttc.CVSlowCanonicalPhaseMomentPackage
open Ttc.CVSharpScoreTransport
open Ttc.CVGaussianWarmFallbackCappedOperational
open Ttc.CVRelativeMeanClippingAssembly
open scoped ENNReal Classical

variable {n : Nat}
abbrev State (n : Nat) := EuclideanSpace Real (Fin n)

/-! ## Step 1 — the sharp phase-score sup, at every index -/

/-- **The sharp per-index sup of the phase score.**  At an interior index it is the sharp
value `exp (R^2/(2 σ_i (n+1)))` of `Ttc.CVSharpScoreTransport.coolRatio_slowSource_le`; at
the terminal index `i + 1 = m` the cooling ratio really is `exp (‖x‖^2/(2 σ_i))`
(`Arlib.GaussianCooling.coolRatio_of_last`), so the loose value is the true sup there and
is what this definition returns. -/
noncomputable def sharpPhaseSup (n : Nat) (R : Real) (sigmaSq : Nat → Real)
    (m i : Nat) : Real :=
  if i + 1 < m then Real.exp (R ^ 2 / (2 * sigmaSq i * ((n : Real) + 1)))
  else Real.exp (R ^ 2 / (2 * sigmaSq i))

theorem sharpPhaseSup_pos {R : Real} {sigmaSq : Nat → Real} (m i : Nat) :
    0 < sharpPhaseSup n R sigmaSq m i := by
  unfold sharpPhaseSup
  split <;> exact Real.exp_pos _

theorem sharpPhaseSup_nonneg {R : Real} {sigmaSq : Nat → Real} (m i : Nat) :
    0 ≤ sharpPhaseSup n R sigmaSq m i := (sharpPhaseSup_pos m i).le

/-- The sharpened sup is never above the loose one that the development currently uses. -/
theorem sharpPhaseSup_le_loose {R : Real} {sigmaSq : Nat → Real} {m i : Nat}
    (hsigma : 0 < sigmaSq i) :
    sharpPhaseSup n R sigmaSq m i ≤ Real.exp (R ^ 2 / (2 * sigmaSq i)) := by
  have hn0 : (0 : Real) ≤ (n : Real) := Nat.cast_nonneg n
  unfold sharpPhaseSup
  split
  · refine Real.exp_le_exp.2 ?_
    refine div_le_div_of_nonneg_left (sq_nonneg R) (by positivity) ?_
    nlinarith [mul_nonneg hsigma.le hn0]
  · exact le_rfl

/-- **The sharp sup bound at every index.**  No hypothesis beyond the body radius: the
interior branch is `Ttc.CVSharpScoreTransport.phaseScore_slowSource_le` and the terminal
branch is `Arlib.GaussianCooling.phaseScore_le`. -/
theorem phaseScore_le_sharpPhaseSup {n : Nat} (hn : 1 ≤ n) {s0 R : Real} (hs0 : 0 < s0)
    {m i : Nat} {K : Set (State n)} (hKR : K ⊆ closedBall (0 : State n) R)
    (x : State n) :
    Arlib.GaussianCooling.phaseScore m (slowSourceSigmaSq n s0) K i x ≤
      sharpPhaseSup n R (slowSourceSigmaSq n s0) m i := by
  unfold sharpPhaseSup
  split
  · rename_i him
    exact phaseScore_slowSource_le hn hs0 him hKR x
  · exact phaseScore_le (slowSourceSigmaSq_pos hn hs0) hKR i x

theorem abs_phaseScore_le_sharpPhaseSup {n : Nat} (hn : 1 ≤ n) {s0 R : Real} (hs0 : 0 < s0)
    {m i : Nat} {K : Set (State n)} (hKR : K ⊆ closedBall (0 : State n) R)
    (x : State n) :
    |Arlib.GaussianCooling.phaseScore m (slowSourceSigmaSq n s0) K i x| ≤
      sharpPhaseSup n R (slowSourceSigmaSq n s0) m i := by
  rw [abs_of_nonneg (phaseScore_nonneg m (slowSourceSigmaSq n s0) K i x)]
  exact phaseScore_le_sharpPhaseSup hn hs0 hKR x

/-- **The single statement valid at every `i < m`**, in the display form the terminal
hypothesis `R^2 ≤ σ_i` buys.  The interior branch cites
`Ttc.CVSharpScoreTransport.coolRatio_slowSource_le` and the terminal branch cites
`Ttc.CVSharpScoreTransport.coolRatio_le_of_last_of_sq_le`.

The hypothesis `hR2` is required **only at the terminal index** and is stated that way:
on the canonical chain `R^2 ≤ N ≤ σ_{m-1}` is exactly what is available
(`Ttc.CVSlowFullBodySourceSchedule.target_le_slowSourceSigmaSq_terminal`), and the
schedule is increasing, so `R^2 ≤ σ_i` is *not* available at small `i`. -/
theorem phaseScore_sharp_le {n : Nat} (hn : 1 ≤ n) {s0 R : Real} (hs0 : 0 < s0)
    {m i : Nat} (him : i < m)
    (hR2 : m ≤ i + 1 → R ^ 2 ≤ slowSourceSigmaSq n s0 i)
    {K : Set (State n)} (hKR : K ⊆ closedBall (0 : State n) R) (x : State n) :
    |Arlib.GaussianCooling.phaseScore m (slowSourceSigmaSq n s0) K i x| ≤
      Real.exp (R ^ 2 / (2 * slowSourceSigmaSq n s0 i * ((n : Real) + 1))) ⊔
        Real.exp (1 / 2) := by
  rw [abs_of_nonneg (phaseScore_nonneg m (slowSourceSigmaSq n s0) K i x)]
  rcases lt_or_ge (i + 1) m with hlt | hge
  · exact le_sup_of_le_left (phaseScore_slowSource_le hn hs0 hlt hKR x)
  · refine le_sup_of_le_right ?_
    by_cases hx : x ∈ K
    · rw [phaseScore_of_mem hx]
      exact coolRatio_le_of_last_of_sq_le him hge (slowSourceSigmaSq_pos hn hs0 i)
        (hR2 hge) (by simpa using mem_closedBall_zero_iff.1 (hKR hx))
    · rw [phaseScore, Set.indicator_of_notMem hx]
      exact (Real.exp_pos _).le

/-! ## Step 1b — the crux: the sharpened transport bound dominates the squared sup

The moment transport consumes the sup as a value: `sq_moment_le_of_tvLe` needs
`ε · B^2 · (1 + 2T) ≤ s · ratio^2` at the *same* `B` that bounds the score.  So the only
thing that matters about `boundSq` is how it compares with `sup^2 * 15`.  At an interior
index the two are **equal**; at the terminal index `R^2 ≤ σ_i` gives
`sup^2 ≤ exp 1 < 3` while `phaseScoreTransportBoundSqSharp ≥ 15`.  Hence the uniform
comparison with the explicit constant three. -/

theorem fifteen_le_phaseScoreTransportBoundSqSharp
    {R : Real} {sigmaSq : Nat → Real} {i : Nat} (hsigma : 0 < sigmaSq i) :
    (15 : Real) ≤ phaseScoreTransportBoundSqSharp n R sigmaSq i := by
  have hn0 : (0 : Real) ≤ (n : Real) := Nat.cast_nonneg n
  have harg : (0 : Real) ≤ R ^ 2 / (2 * sigmaSq i * ((n : Real) + 1)) := by
    have : (0 : Real) < 2 * sigmaSq i * ((n : Real) + 1) := by positivity
    positivity
  have hexp : (1 : Real) ≤ Real.exp (R ^ 2 / (2 * sigmaSq i * ((n : Real) + 1))) := by
    simpa using Real.exp_le_exp.2 harg
  unfold phaseScoreTransportBoundSqSharp
  nlinarith [hexp]

/-- **The crux.**  The sharpened transport bound dominates the squared sharp sup up to the
absolute constant three, at **every** index `i < m` — the interior indices with room to
spare (there the two sides differ by exactly the factor three), the terminal index because
`R^2 ≤ σ_i` makes the true sup at most `exp (1/2)`. -/
theorem sharpPhaseSup_sq_mul_le_three_mul {n : Nat} (hn : 1 ≤ n) {s0 R : Real}
    (hs0 : 0 < s0) {m i : Nat}
    (hR2 : m ≤ i + 1 → R ^ 2 ≤ slowSourceSigmaSq n s0 i) :
    sharpPhaseSup n R (slowSourceSigmaSq n s0) m i ^ 2 * (1 + 2 * 7) ≤
      3 * phaseScoreTransportBoundSqSharp n R (slowSourceSigmaSq n s0) i := by
  have hsigma : 0 < slowSourceSigmaSq n s0 i := slowSourceSigmaSq_pos hn hs0 i
  have h15 : (15 : Real) ≤ phaseScoreTransportBoundSqSharp n R (slowSourceSigmaSq n s0) i :=
    fifteen_le_phaseScoreTransportBoundSqSharp hsigma
  unfold sharpPhaseSup
  split
  · have heq : Real.exp (R ^ 2 / (2 * slowSourceSigmaSq n s0 i * ((n : Real) + 1))) ^ 2 *
        (1 + 2 * 7) = phaseScoreTransportBoundSqSharp n R (slowSourceSigmaSq n s0) i := rfl
    rw [heq]
    linarith
  · rename_i hge
    have hge' : m ≤ i + 1 := by omega
    have hhalf : R ^ 2 / (2 * slowSourceSigmaSq n s0 i) ≤ 1 / 2 := by
      rw [div_le_div_iff₀ (by linarith : (0 : Real) < 2 * slowSourceSigmaSq n s0 i)
        (by norm_num : (0 : Real) < 2)]
      nlinarith [hR2 hge']
    have hexp : Real.exp (R ^ 2 / (2 * slowSourceSigmaSq n s0 i)) ≤ Real.exp (1 / 2) :=
      Real.exp_le_exp.2 hhalf
    have hexp0 : (0 : Real) < Real.exp (R ^ 2 / (2 * slowSourceSigmaSq n s0 i)) :=
      Real.exp_pos _
    have hsq : Real.exp (R ^ 2 / (2 * slowSourceSigmaSq n s0 i)) ^ 2 ≤ Real.exp 1 := by
      have := pow_le_pow_left₀ hexp0.le hexp 2
      rwa [show Real.exp (1 / 2 : Real) ^ 2 = Real.exp 1 by
        rw [← Real.exp_nat_mul]; norm_num] at this
    have he3 : Real.exp 1 ≤ 3 := by
      have := Real.exp_one_lt_d9
      linarith
    nlinarith [hsq, he3, h15]

/-! ## Step 2 — the sharp squared-observable tail budget -/

/-- **The sharp analogue of `Ttc.CVSlowCanonicalMomentBinders.slowCanonical_htailBudget`.**
The loose sup `exp (R^2/(2 σ_i))` is replaced by the sharp per-index sup, at the very same
floor `Ttc.CVSlowCanonicalUniformParameters.slowUniformMeanTailFloor` and the very same
comparison constant `C := 2`.  The arithmetic is strictly easier than the original's,
because `sharpPhaseSup ≤ exp (R^2/(2 σ_i))`. -/
theorem slowSharp_htailBudget (hn : 1 ≤ n) (m k : Nat) {eps R : Real}
    {K : Set (State n)} (hK : MeasurableSet K)
    (hball : ball (0 : State n) 1 ⊆ K) (hfin : volume K ≠ ⊤) :
    ∀ i : Fin m,
      slowUniformMeanTailFloor n m k eps R *
        (sharpPhaseSup n R (slowSourceSigmaSq n (slowSourceInitialVariance n)) m
          (i : Nat) * 15) ≤
      phaseMomentSlackSeven m
        (slowSourceSigmaSq n (slowSourceInitialVariance n)) K
        (fun _ ↦ 2) (i : Nat) / 2 := by
  intro i
  have hs0 : 0 < slowSourceInitialVariance n := slowSourceInitialVariance_pos hn
  have hsigma : 0 < slowSourceSigmaSq n (slowSourceInitialVariance n) (i : Nat) :=
    slowSourceSigmaSq_pos hn hs0 (i : Nat)
  have hfloor0 : 0 ≤ slowUniformMeanTailFloor n m k eps R := by
    unfold slowUniformMeanTailFloor slowCanonicalJointTailFloor
    refine le_min ?_ (by positivity)
    exact div_nonneg
      (Ttc.CVGaussianScoreAwareMeanBudget.scoreAwareMeanEta_nonneg m k eps) (by norm_num)
  have hsharp := sharpPhaseSup_le_loose
    (n := n) (R := R) (sigmaSq := slowSourceSigmaSq n (slowSourceInitialVariance n))
    (m := m) (i := (i : Nat)) hsigma
  have hstep :
      slowUniformMeanTailFloor n m k eps R *
        (sharpPhaseSup n R (slowSourceSigmaSq n (slowSourceInitialVariance n)) m
          (i : Nat) * 15) ≤
      slowUniformMeanTailFloor n m k eps R *
        (Real.exp (R ^ 2 /
          (2 * slowSourceSigmaSq n (slowSourceInitialVariance n) (i : Nat))) * 15) := by
    have : sharpPhaseSup n R (slowSourceSigmaSq n (slowSourceInitialVariance n)) m
        (i : Nat) * 15 ≤
      Real.exp (R ^ 2 /
        (2 * slowSourceSigmaSq n (slowSourceInitialVariance n) (i : Nat))) * 15 := by
      nlinarith
    exact mul_le_mul_of_nonneg_left this hfloor0
  exact hstep.trans
    (Ttc.CVSlowCanonicalMomentBinders.slowCanonical_htailBudget hn m k hK hball hfin i)

/-! ## Step 3a — the moment transport at an arbitrary sup bound

`Arlib.GaussianCooling.phaseScore_interior_sq_moment_le_of_tvLe` and the two Ttc lemmas
built on it (`Ttc.CVGaussianFactorSevenAssembly.operational_phaseScore_sq_moment_le_factor`,
`Ttc.CVGaussianSourceWeightedMoment.operational_path_phaseScore_memLp_and_sq_moment_le_factor_of_targetTV`)
hard-code the sup as `exp (R^2/(2 σ_i))`.  The Arlib workhorse one level down,
`Arlib.GaussianCooling.sq_moment_le_of_tvLe_map`, is already generic in the bound `B`, so
the sharp versions are obtained by re-deriving these three at a general `B` — no transport
argument is re-proved. -/

theorem phaseScore_interior_sq_moment_le_of_tvLe_bound
    {Omega : Type*} [MeasurableSpace Omega]
    {mu : Measure Omega} [IsProbabilityMeasure mu]
    {chainLength : Nat} {sigmaSq : Nat → Real} {i : Nat}
    {K : Set (State n)} {X : Omega → State n} {e : ENNReal}
    (hsigma : ∀ j, 0 < sigmaSq j) (hKc : Convex Real K)
    (hball : ball (0 : State n) 1 ⊆ K) (hfin : volume K ≠ ⊤)
    (hX : Measurable X)
    (hTV : TVLe (Measure.map X mu) (coolLaw chainLength sigmaSq K i) e)
    (he : e ≠ ⊤) {B : Real} (hB : 0 < B)
    (hfB : ∀ x, phaseScore chainLength sigmaSq (interior K) i x ≤ B)
    {C s : Real} (hC : 0 ≤ C) (hs : 0 ≤ s)
    (hexact : ∫ x, phaseScore chainLength sigmaSq (interior K) i x ^ 2
        ∂(coolLaw chainLength sigmaSq K i) ≤
      C * (∫ x, phaseScore chainLength sigmaSq (interior K) i x
        ∂(coolLaw chainLength sigmaSq K i)) ^ 2)
    (hslack : e.toReal * (B ^ 2 * (1 + 2 * (C + s))) ≤
      s * (chain chainLength sigmaSq K (i + 1) /
        chain chainLength sigmaSq K i) ^ 2) :
    ∫ omega, phaseScore chainLength sigmaSq (interior K) i (X omega) ^ 2 ∂mu ≤
      (C + s) * (∫ omega,
        phaseScore chainLength sigmaSq (interior K) i (X omega) ∂mu) ^ 2 := by
  haveI := coolLaw_isProbabilityMeasure (m := chainLength) (σsq := sigmaSq)
    hsigma hball hfin i
  have hmean := integral_phaseScore_interior_coolLaw (m := chainLength) (i := i)
    hsigma hKc hball hfin
  exact sq_moment_le_of_tvLe_map hX hTV he hB
    (measurable_phaseScore isOpen_interior.measurableSet i)
    (phaseScore_nonneg chainLength sigmaSq (interior K) i) hfB hC hs hexact
    (by rw [hmean]; exact hslack)

/-- Target-factor form at an arbitrary sup bound: the sharp analogue of
`Ttc.CVGaussianFactorSevenAssembly.operational_phaseScore_sq_moment_le_factor`. -/
theorem operational_phaseScore_sq_moment_le_factor_bound
    {Omega : Type*} [MeasurableSpace Omega]
    {mu : Measure Omega} [IsProbabilityMeasure mu]
    {chainLength : Nat} {sigmaSq : Nat → Real} {i : Nat}
    {K : Set (State n)} {X : Omega → State n} {e : ENNReal}
    (hsigma : ∀ j, 0 < sigmaSq j) (hKc : Convex Real K)
    (hball : ball (0 : State n) 1 ⊆ K) (hfin : volume K ≠ ⊤)
    (hX : Measurable X)
    (hTV : TVLe (Measure.map X mu) (coolLaw chainLength sigmaSq K i) e)
    (he : e ≠ ⊤) {B : Real} (hB : 0 < B)
    (hfB : ∀ x, phaseScore chainLength sigmaSq (interior K) i x ≤ B)
    {C T : Real} (hC0 : 0 ≤ C) (hCT : C ≤ T)
    (hexact : ∫ x, phaseScore chainLength sigmaSq (interior K) i x ^ 2
        ∂(coolLaw chainLength sigmaSq K i) ≤
      C * (∫ x, phaseScore chainLength sigmaSq (interior K) i x
        ∂(coolLaw chainLength sigmaSq K i)) ^ 2)
    (hslack : e.toReal * (B ^ 2 * (1 + 2 * T)) ≤
      (T - C) * (chain chainLength sigmaSq K (i + 1) /
        chain chainLength sigmaSq K i) ^ 2) :
    ∫ omega, phaseScore chainLength sigmaSq (interior K) i (X omega) ^ 2 ∂mu ≤
      T * (∫ omega,
        phaseScore chainLength sigmaSq (interior K) i (X omega) ∂mu) ^ 2 := by
  have hgap : 0 ≤ T - C := sub_nonneg.2 hCT
  have heq : C + (T - C) = T := by ring
  have hmain := phaseScore_interior_sq_moment_le_of_tvLe_bound hsigma hKc hball hfin
    hX hTV he hB hfB hC0 hgap hexact
    (by rw [heq]; exact hslack)
  simpa only [heq] using hmain

/-- The sharp analogue of
`Ttc.CVGaussianSourceWeightedMoment.operational_path_phaseScore_memLp_and_sq_moment_le_factor_of_targetTV`,
at an arbitrary sup bound `B`.  Both consumers of the sup — the `L^2` membership and the
transport slack — are fed the same `B`. -/
theorem operational_path_phaseScore_memLp_and_sq_moment_le_factor_of_targetTV_bound
    {Seed : Type*} [MeasurableSpace Seed]
    {k mPhases chainLength : Nat}
    {Q : Nat → Kernel Seed (State n × Seed)} [∀ i, IsMarkovKernel (Q i)]
    {mu0 : Measure (State n × Seed)} [IsProbabilityMeasure mu0]
    {V : Nat → (Fin k → Nat → State n × Seed) → Real} {eta : Real}
    (hop : IndependentStreamOperational k (stateScheduleFromSeed Q)
      Q Prod.snd mu0 V mPhases eta)
    {sigmaSq : Nat → Real} {i : Nat} {K : Set (State n)}
    (hsigma : ∀ j, 0 < sigmaSq j) (hKc : Convex Real K)
    (hball : ball (0 : State n) 1 ⊆ K) (hfin : volume K ≠ ⊤)
    {targetError : ENNReal}
    (htargetTV : TVLe (Measure.map Prod.fst (hop.tau i))
      (coolLaw chainLength sigmaSq K i) targetError)
    (htargetError : targetError ≠ ⊤)
    {B : Real} (hB : 0 < B)
    (hfB : ∀ x, phaseScore chainLength sigmaSq (interior K) i x ≤ B)
    {C T : Real} (hC0 : 0 ≤ C) (hCT : C ≤ T)
    (hexact : ∫ x, phaseScore chainLength sigmaSq (interior K) i x ^ 2
        ∂(coolLaw chainLength sigmaSq K i) ≤
      C * (∫ x, phaseScore chainLength sigmaSq (interior K) i x
        ∂(coolLaw chainLength sigmaSq K i)) ^ 2)
    (hslack : (hop.mixError i + targetError).toReal * (B ^ 2 * (1 + 2 * T)) ≤
      (T - C) * (chain chainLength sigmaSq K (i + 1) /
        chain chainLength sigmaSq K i) ^ 2) :
    let pathLaw := inhomogeneousPathMeasure (stateScheduleFromSeed Q) mu0
    let g := fun omega : Nat → State n × Seed ↦
      phaseScore chainLength sigmaSq (interior K) i (omega (i + 1)).1
    MemLp g 2 pathLaw ∧
      (∫ omega, (g omega) ^ 2 ∂pathLaw) ≤
        T * (∫ omega, g omega ∂pathLaw) ^ 2 := by
  dsimp only
  let pathLaw := inhomogeneousPathMeasure (stateScheduleFromSeed Q) mu0
  let X : (Nat → State n × Seed) → State n := fun omega ↦ (omega (i + 1)).1
  have hfm := measurable_phaseScore (m := chainLength)
    (σsq := sigmaSq) (K := interior K) isOpen_interior.measurableSet i
  have hbound : ∀ x, |phaseScore chainLength sigmaSq (interior K) i x| ≤ B := by
    intro x
    rw [abs_of_nonneg (phaseScore_nonneg chainLength sigmaSq (interior K) i x)]
    exact hfB x
  constructor
  · exact memLp_pathScore_of_bounded hfm hbound i
  · have htv0 := tvLe_operational_score_eval_succ hop i
    have htv : TVLe (Measure.map X pathLaw)
        (coolLaw chainLength sigmaSq K i)
        (hop.mixError i + targetError) := htv0.trans htargetTV
    exact operational_phaseScore_sq_moment_le_factor_bound hsigma hKc hball hfin
      (by fun_prop) htv
      (ENNReal.add_ne_top.2 ⟨hop.mixError_ne_top i, htargetError⟩)
      hB hfB hC0 hCT hexact hslack

/-! ## Step 3b — the phasewise second-moment split at the sharpened bound

The sharp analogue of
`Ttc.CVRAwareGlobalRadius.scoreAwareMix_add_slowTargetError_rAware_phaseBound_le`.  Two
halves, and only the first one changes:

* **mixing**: `mix · boundSqSharp ≤ slack/6` (`scoreAwareMixError_mul_boundSq_le_slack`,
  generic in the slack), and `sup^2 · 15 ≤ 3 · boundSqSharp`
  (`sharpPhaseSup_sq_mul_le_three_mul`), so `mix · (sup^2 · 15) ≤ slack/2`.  The `/6` is
  the entire cost of the terminal index;
* **radial tail**: never touches `boundSq`.  `tail · loose ≤ b` and `sup ≤ loose` give
  `tail · (sup^2 · 15) ≤ b · (sup · 15) ≤ slack/2`, i.e. exactly the sharp tail budget of
  Step 2. -/
theorem scoreAwareMix_add_slowTargetError_sharp_phaseBound_le
    {n m k chainLength i : Nat} (hn : 1 ≤ n)
    {eps R s0 b : Real} {sigmaSq : Nat → Real}
    {K : Set (State n)} {C : Nat → Real}
    (heps : 0 < eps) (heps1 : eps ≤ 1) (hs0 : 0 < s0) (hb : 0 < b)
    (hi : i < m) (hsigma : ∀ j, 0 < sigmaSq j)
    (hball : ball (0 : State n) 1 ⊆ K) (hfin : volume K ≠ ⊤) (hC7 : ∀ j, C j < 7)
    (hsigmaSlow : sigmaSq = slowSourceSigmaSq n s0)
    (hR2 : chainLength ≤ i + 1 → R ^ 2 ≤ sigmaSq i)
    (hbudget : b * (sharpPhaseSup n R sigmaSq chainLength i * 15) ≤
      phaseMomentSlackSeven chainLength sigmaSq K C i / 2) :
    (scoreAwareMixError (m + 1) k (eps / 2)
        (fun j ↦ phaseMomentSlackSeven chainLength sigmaSq K C j / 6)
        (phaseScoreTransportBoundSqSharp n R sigmaSq) i +
      slowTargetError n (rAwareGlobalRadiusQ n R s0 b) m i).toReal *
        (sharpPhaseSup n R sigmaSq chainLength i ^ 2 * (1 + 2 * 7)) ≤
      phaseMomentSlackSeven chainLength sigmaSq K C i := by
  subst hsigmaSlow
  set sup := sharpPhaseSup n R (slowSourceSigmaSq n s0) chainLength i with hsupdef
  set slack := phaseMomentSlackSeven chainLength (slowSourceSigmaSq n s0) K C with hslackdef
  have hslackPos : ∀ j, 0 < slack j :=
    phaseMomentSlackSeven_pos hsigma hball hfin hC7
  have hboundPos : ∀ j, 0 < phaseScoreTransportBoundSqSharp n R
      (slowSourceSigmaSq n s0) j := phaseScoreTransportBoundSqSharp_pos
  have hsup0 : 0 ≤ sup := sharpPhaseSup_nonneg _ _
  -- the mixing half
  have hmixbase := scoreAwareMixError_mul_boundSq_le_slack
    (m := m + 1) (k := k) (eps := eps / 2)
    (slack := fun j ↦ slack j / 6)
    (boundSq := phaseScoreTransportBoundSqSharp n R (slowSourceSigmaSq n s0))
    (by positivity) (by linarith) (fun j ↦ div_pos (hslackPos j) (by norm_num))
    hboundPos i
  have hcrux : sup ^ 2 * (1 + 2 * 7) ≤
      3 * phaseScoreTransportBoundSqSharp n R (slowSourceSigmaSq n s0) i :=
    sharpPhaseSup_sq_mul_le_three_mul hn hs0 hR2
  have hmix0 : 0 ≤ (scoreAwareMixError (m + 1) k (eps / 2)
      (fun j ↦ slack j / 6)
      (phaseScoreTransportBoundSqSharp n R (slowSourceSigmaSq n s0)) i).toReal :=
    ENNReal.toReal_nonneg
  have hmix : (scoreAwareMixError (m + 1) k (eps / 2)
      (fun j ↦ slack j / 6)
      (phaseScoreTransportBoundSqSharp n R (slowSourceSigmaSq n s0)) i).toReal *
      (sup ^ 2 * (1 + 2 * 7)) ≤ slack i / 2 := by
    nlinarith [hmixbase, hcrux, hmix0]
  -- the radial-tail half
  have hloose := slowTargetError_rAware_scaled_le (n := n) (m := m) (i := i)
    hn (R := R) (s0 := s0) (b := b) (target := b) hs0 hb hi le_rfl
  have hsupLoose : sup ≤ Real.exp (R ^ 2 / (2 * slowSourceSigmaSq n s0 i)) :=
    sharpPhaseSup_le_loose (slowSourceSigmaSq_pos hn hs0 i)
  have htail0 : 0 ≤ (slowTargetError n (rAwareGlobalRadiusQ n R s0 b) m i).toReal :=
    ENNReal.toReal_nonneg
  have htail : (slowTargetError n (rAwareGlobalRadiusQ n R s0 b) m i).toReal *
      (sup ^ 2 * (1 + 2 * 7)) ≤ slack i / 2 := by
    have hstep : (slowTargetError n (rAwareGlobalRadiusQ n R s0 b) m i).toReal *
        (sup ^ 2 * (1 + 2 * 7)) ≤
        ((slowTargetError n (rAwareGlobalRadiusQ n R s0 b) m i).toReal *
          Real.exp (R ^ 2 / (2 * slowSourceSigmaSq n s0 i))) * (sup * 15) := by
      have hkey : 0 ≤ ((slowTargetError n (rAwareGlobalRadiusQ n R s0 b) m i).toReal *
          sup) * (Real.exp (R ^ 2 / (2 * slowSourceSigmaSq n s0 i)) - sup) :=
        mul_nonneg (mul_nonneg htail0 hsup0) (by linarith)
      nlinarith [hkey]
    refine hstep.trans (le_trans ?_ hbudget)
    exact mul_le_mul_of_nonneg_right hloose (by positivity)
  rw [ENNReal.toReal_add (scoreAwareMixError_ne_top _ _ _ _ _ _)
    (slowTargetError_ne_top n _ m i)]
  calc
    _ = (scoreAwareMixError (m + 1) k (eps / 2)
          (fun j ↦ slack j / 6)
          (phaseScoreTransportBoundSqSharp n R (slowSourceSigmaSq n s0)) i).toReal *
          (sup ^ 2 * (1 + 2 * 7)) +
        (slowTargetError n (rAwareGlobalRadiusQ n R s0 b) m i).toReal *
          (sup ^ 2 * (1 + 2 * 7)) := by ring
    _ ≤ slack i / 2 + slack i / 2 := add_le_add hmix htail
    _ = slack i := by ring

/-! ## Step 3c — the factor-seven phase moment at the sharpened bound -/

/-- **The sharp analogue of
`Ttc.CVSlowCanonicalPhaseMomentPackage.operational_slowCanonical_phaseScore_factorSeven`.**
Same inputs, with three substitutions and nothing else:

* `boundSq := phaseScoreTransportBoundSqSharp n R sigmaSq` in the mixing-error binder
  (this is the payoff: on the canonical schedule the exponent loses its factor `n`);
* the mixing-slack binder is `phaseMomentSlackSeven … / 6` rather than `… / 2` — forced,
  see the module docstring;
* `htailBudget` is stated at the sharp per-index sup, which is *weaker* than the original.

`hR2` is needed **only at the terminal index** `i + 1 = m`, where the loose bound is the
true sup; it is exactly what the canonical chain supplies. -/
theorem operational_slowCanonical_phaseScore_factorSeven_sharp
    {k m : Nat} {Q : Nat → Kernel (State n) (State n × State n)}
    [∀ i, IsMarkovKernel (Q i)]
    {mu0 : Measure (State n × State n)} [IsProbabilityMeasure mu0]
    {V : Nat → (Fin k → Nat → State n × State n) → Real}
    {estimatorEps eps R s0 b : Real}
    (hop : IndependentStreamOperational k (stateScheduleFromSeed Q) Q Prod.snd
      mu0 V m estimatorEps)
    (hn : 1 ≤ n) (heps : 0 < eps) (heps1 : eps ≤ 1)
    (hs0 : 0 < s0) (hb : 0 < b)
    {sigmaSq : Nat → Real} (hsigma : ∀ j, 0 < sigmaSq j)
    {K : Set (State n)} (hKc : Convex Real K)
    (hball : ball (0 : State n) 1 ⊆ K) (hfin : volume K ≠ ⊤)
    (hKR : K ⊆ closedBall (0 : State n) R)
    {C : Nat → Real} (hC0 : ∀ j, 0 ≤ C j) (hC7 : ∀ j, C j < 7)
    (hmixError : ∀ j, hop.mixError j = activeReferenceMixError (m + 1)
      (scoreAwareMixError (m + 1) k (eps / 2)
        (fun t ↦ phaseMomentSlackSeven m sigmaSq K C t / 6)
        (phaseScoreTransportBoundSqSharp n R sigmaSq)) j)
    (htargetTV : ∀ j, TVLe (Measure.map Prod.fst (hop.tau j))
      (coolLaw m sigmaSq K j)
      (slowTargetError n (rAwareGlobalRadiusQ n R s0 b) m j))
    (hsigmaSlow : sigmaSq = slowSourceSigmaSq n s0)
    (hexact : ∀ j,
      ∫ x, phaseScore m sigmaSq (interior K) j x ^ 2 ∂(coolLaw m sigmaSq K j) ≤
        C j * (∫ x, phaseScore m sigmaSq (interior K) j x
          ∂(coolLaw m sigmaSq K j)) ^ 2)
    (hR2 : ∀ i : Fin m, m ≤ (i : Nat) + 1 → R ^ 2 ≤ sigmaSq (i : Nat))
    (htailBudget : ∀ i : Fin m,
      b * (sharpPhaseSup n R sigmaSq m (i : Nat) * 15) ≤
        phaseMomentSlackSeven m sigmaSq K C (i : Nat) / 2)
    (i : Fin m) :
    let pathLaw := inhomogeneousPathMeasure (stateScheduleFromSeed Q) mu0
    let g := fun omega : Nat → State n × State n ↦
      phaseScore m sigmaSq (interior K) (i : Nat) (omega ((i : Nat) + 1)).1
    MemLp g 2 pathLaw ∧
      (∫ omega, (g omega) ^ 2 ∂pathLaw) ≤
        7 * (∫ omega, g omega ∂pathLaw) ^ 2 := by
  subst hsigmaSlow
  have hmix : hop.mixError (i : Nat) = scoreAwareMixError (m + 1) k (eps / 2)
      (fun t ↦ phaseMomentSlackSeven m (slowSourceSigmaSq n s0) K C t / 6)
      (phaseScoreTransportBoundSqSharp n R (slowSourceSigmaSq n s0)) (i : Nat) := by
    rw [hmixError (i : Nat), activeReferenceMixError,
      if_pos (by omega : (i : Nat) + 1 < m + 1)]
  have htransport := scoreAwareMix_add_slowTargetError_sharp_phaseBound_le
    (n := n) (m := m) (k := k) (chainLength := m) (i := (i : Nat)) hn
    (eps := eps) (R := R) (s0 := s0) (b := b)
    (sigmaSq := slowSourceSigmaSq n s0) (K := K) (C := C)
    heps heps1 hs0 hb i.isLt hsigma hball hfin hC7 rfl (hR2 i) (htailBudget i)
  rw [← hmix] at htransport
  exact operational_path_phaseScore_memLp_and_sq_moment_le_factor_of_targetTV_bound
    (C := C i) (T := 7) hop hsigma hKc hball hfin
    (htargetTV i) (slowTargetError_ne_top n _ m i)
    (sharpPhaseSup_pos m (i : Nat))
    (fun x ↦ phaseScore_le_sharpPhaseSup hn hs0 (interior_subset.trans hKR) x)
    (hC0 i) (hC7 i).le (hexact i)
    (by simpa only [phaseMomentSlackSeven] using htransport)

/-- **The sharp analogue of
`Ttc.CVSlowCanonicalPhaseMomentPackage.operational_slowCanonical_positiveScalar_factorSeven_upto`.**
The scalar factor-seven statement on exactly the estimator prefix, with the sharpened
score transport bound in the mixing-error binder. -/
theorem operational_slowCanonical_positiveScalar_factorSeven_sharp_upto
    {k m : Nat} {Q : Nat → Kernel (State n) (State n × State n)}
    [∀ i, IsMarkovKernel (Q i)]
    {mu0 : Measure (State n × State n)} [IsProbabilityMeasure mu0]
    {V : Nat → (Fin k → Nat → State n × State n) → Real}
    {estimatorEps eps R s0 b : Real}
    (hop : IndependentStreamOperational k (stateScheduleFromSeed Q) Q Prod.snd
      mu0 V m estimatorEps)
    (hn : 1 ≤ n) (heps : 0 < eps) (heps1 : eps ≤ 1)
    (hs0 : 0 < s0) (hb : 0 < b)
    {sigmaSq : Nat → Real} (hsigma : ∀ j, 0 < sigmaSq j)
    {K : Set (State n)} (hKc : Convex Real K)
    (hball : ball (0 : State n) 1 ⊆ K) (hfin : volume K ≠ ⊤)
    (hKR : K ⊆ closedBall (0 : State n) R)
    {C : Nat → Real} (hC0 : ∀ j, 0 ≤ C j) (hC7 : ∀ j, C j < 7)
    (hmixError : ∀ j, hop.mixError j = activeReferenceMixError (m + 1)
      (scoreAwareMixError (m + 1) k (eps / 2)
        (fun t ↦ phaseMomentSlackSeven m sigmaSq K C t / 6)
        (phaseScoreTransportBoundSqSharp n R sigmaSq)) j)
    (htargetTV : ∀ j, TVLe (Measure.map Prod.fst (hop.tau j))
      (coolLaw m sigmaSq K j)
      (slowTargetError n (rAwareGlobalRadiusQ n R s0 b) m j))
    (hsigmaSlow : sigmaSq = slowSourceSigmaSq n s0)
    (hexact : ∀ j,
      ∫ x, phaseScore m sigmaSq (interior K) j x ^ 2 ∂(coolLaw m sigmaSq K j) ≤
        C j * (∫ x, phaseScore m sigmaSq (interior K) j x
          ∂(coolLaw m sigmaSq K j)) ^ 2)
    (hR2 : ∀ i : Fin m, m ≤ (i : Nat) + 1 → R ^ 2 ≤ sigmaSq (i : Nat))
    (htailBudget : ∀ i : Fin m,
      b * (sharpPhaseSup n R sigmaSq m (i : Nat) * 15) ≤
        phaseMomentSlackSeven m sigmaSq K C (i : Nat) / 2) :
    ∀ j, j ≤ m →
      MemLp (positiveScalarPhaseFamilyChainLength (Seed := State n)
          m sigmaSq K j) 2
        (inhomogeneousPathMeasure (stateScheduleFromSeed Q) mu0) ∧
      ∫ omega,
          (positiveScalarPhaseFamilyChainLength (Seed := State n)
            m sigmaSq K j omega) ^ 2
          ∂(inhomogeneousPathMeasure (stateScheduleFromSeed Q) mu0) ≤
        7 * (∫ omega,
          positiveScalarPhaseFamilyChainLength (Seed := State n)
            m sigmaSq K j omega
          ∂(inhomogeneousPathMeasure (stateScheduleFromSeed Q) mu0)) ^ 2 := by
  intro j hj
  cases j with
  | zero =>
      constructor
      · simpa [positiveScalarPhaseFamilyChainLength] using
          (memLp_const
            (μ := inhomogeneousPathMeasure (stateScheduleFromSeed Q) mu0)
            (c := (1 : Real)) (p := (2 : ENNReal)))
      · simp [positiveScalarPhaseFamilyChainLength]
  | succ i =>
      have hi : i < m := Nat.lt_of_succ_le hj
      change
        MemLp (fun omega : Nat → State n × State n ↦
          phaseScore m sigmaSq (interior K) i (omega (i + 1)).1) 2
            (inhomogeneousPathMeasure (stateScheduleFromSeed Q) mu0) ∧
        ∫ omega,
            (phaseScore m sigmaSq (interior K) i (omega (i + 1)).1) ^ 2
            ∂(inhomogeneousPathMeasure (stateScheduleFromSeed Q) mu0) ≤
          7 * (∫ omega,
            phaseScore m sigmaSq (interior K) i (omega (i + 1)).1
            ∂(inhomogeneousPathMeasure (stateScheduleFromSeed Q) mu0)) ^ 2
      exact operational_slowCanonical_phaseScore_factorSeven_sharp hop hn heps heps1
        hs0 hb hsigma hKc hball hfin hKR hC0 hC7 hmixError htargetTV
        hsigmaSlow hexact hR2 htailBudget ⟨i, hi⟩

/-! ## Step 3d — the source-schedule and canonical specializations

Here the two remaining analytic binders are discharged exactly as in the original:
`hexact` by `Ttc.CVSlowGaussianPhaseMoment.slowSource_phaseScore_interior_sq_moment_le_two`,
and the terminal-index hypothesis `hR2` by `R^2 ≤ N` together with
`Ttc.CVSlowFullBodySourceSchedule.target_le_slowSourceSigmaSq_terminal` — which is what
makes the terminal index of the canonical chain the one place where `R^2 ≤ σ_i` holds. -/

/-- The sharp analogue of
`Ttc.CVSlowCanonicalPhaseMomentPackage.operational_slowSource_positiveScalar_factorSeven_upto`. -/
theorem operational_slowSource_positiveScalar_factorSeven_sharp_upto
    {n k : Nat} (hn : 3 ≤ n) {N s0 R b eps : Real}
    (hN : 0 < N) (hs0 : 0 < s0) (hsN : s0 ≤ N) (hR2 : R ^ 2 ≤ N)
    (hb : 0 < b) (heps : 0 < eps) (heps1 : eps ≤ 1)
    {K : Set (State n)} (hK : MeasurableSet K) (hKc : Convex Real K)
    (hball : ball (0 : State n) 1 ⊆ K) (hfin : volume K ≠ ⊤)
    (hKR : K ⊆ closedBall (0 : State n) R)
    {Q : Nat → Kernel (State n) (State n × State n)}
    [∀ i, IsMarkovKernel (Q i)]
    {mu0 : Measure (State n × State n)} [IsProbabilityMeasure mu0]
    {V : Nat → (Fin k → Nat → State n × State n) → Real}
    {estimatorEps : Real}
    (hop : IndependentStreamOperational k (stateScheduleFromSeed Q) Q Prod.snd
      mu0 V (slowSourcePhases n N s0 + 1) estimatorEps)
    (hmixError : ∀ j, hop.mixError j =
      activeReferenceMixError (slowSourcePhases n N s0 + 2)
        (scoreAwareMixError (slowSourcePhases n N s0 + 2) k (eps / 2)
          (fun t ↦ phaseMomentSlackSeven (slowSourcePhases n N s0 + 1)
            (slowSourceSigmaSq n s0) K (fun _ ↦ 2) t / 6)
          (phaseScoreTransportBoundSqSharp n R (slowSourceSigmaSq n s0))) j)
    (htargetTV : ∀ j, TVLe (Measure.map Prod.fst (hop.tau j))
      (coolLaw (slowSourcePhases n N s0 + 1) (slowSourceSigmaSq n s0) K j)
      (slowTargetError n (rAwareGlobalRadiusQ n R s0 b)
        (slowSourcePhases n N s0 + 1) j))
    (htailBudget : ∀ i : Fin (slowSourcePhases n N s0 + 1),
      b * (sharpPhaseSup n R (slowSourceSigmaSq n s0)
          (slowSourcePhases n N s0 + 1) (i : Nat) * 15) ≤
        phaseMomentSlackSeven (slowSourcePhases n N s0 + 1)
          (slowSourceSigmaSq n s0) K (fun _ ↦ 2) (i : Nat) / 2) :
    ∀ j, j ≤ slowSourcePhases n N s0 + 1 →
      MemLp (positiveScalarPhaseFamilyChainLength (Seed := State n)
          (slowSourcePhases n N s0 + 1) (slowSourceSigmaSq n s0) K j) 2
        (inhomogeneousPathMeasure (stateScheduleFromSeed Q) mu0) ∧
      ∫ omega,
          (positiveScalarPhaseFamilyChainLength (Seed := State n)
            (slowSourcePhases n N s0 + 1) (slowSourceSigmaSq n s0) K j omega) ^ 2
          ∂(inhomogeneousPathMeasure (stateScheduleFromSeed Q) mu0) ≤
        7 * (∫ omega,
          positiveScalarPhaseFamilyChainLength (Seed := State n)
            (slowSourcePhases n N s0 + 1) (slowSourceSigmaSq n s0) K j omega
          ∂(inhomogeneousPathMeasure (stateScheduleFromSeed Q) mu0)) ^ 2 := by
  apply operational_slowCanonical_positiveScalar_factorSeven_sharp_upto hop
    (by omega) heps heps1 hs0 hb
    (slowSourceSigmaSq_pos (by omega) hs0) hKc hball hfin hKR
    (fun _ ↦ by norm_num) (fun _ ↦ by norm_num) hmixError htargetTV rfl
  · intro j
    exact Ttc.CVSlowGaussianPhaseMoment.slowSource_phaseScore_interior_sq_moment_le_two
      hn hN hs0 hsN hR2 hK hKc hball hfin hKR j
  · intro i hterm
    have hi := i.isLt
    have hidx : (i : Nat) = slowSourcePhases n N s0 := by omega
    rw [hidx]
    exact hR2.trans
      (target_le_slowSourceSigmaSq_terminal (by omega : 1 ≤ n) hN hs0 hsN)
  · exact htailBudget

/-- **The canonical sharp factor-seven package**, at
`boundSq := Ttc.CVSharpScoreTransport.slowSharpBoundSq n R` — the sharpened transport
bound of `Ttc.CVSharpScoreTransport` verbatim — and at the tail floor
`Ttc.CVSlowCanonicalUniformParameters.slowUniformMeanTailFloor` that the development
already selects.  Compared with
`Ttc.CVSlowCanonicalMomentBinders.slowCanonical_scalarFactorSeven` the *only* change is
`boundSq` (dimension-free exponent instead of `exp (8 n R^2)`) and, forced by the single
terminal index, the mixing-slack constant `/2 → /6`. -/
theorem operational_slowCanonical_positiveScalar_factorSeven_sharpBound
    {n k : Nat} (hn : 3 ≤ n) {N R eps : Real}
    (hN : 0 < N) (hsN : slowSourceInitialVariance n ≤ N) (hR2 : R ^ 2 ≤ N)
    (heps : 0 < eps) (heps1 : eps ≤ 1)
    {K : Set (State n)} (hK : MeasurableSet K) (hKc : Convex Real K)
    (hball : ball (0 : State n) 1 ⊆ K) (hfin : volume K ≠ ⊤)
    (hKR : K ⊆ closedBall (0 : State n) R)
    {Q : Nat → Kernel (State n) (State n × State n)}
    [∀ i, IsMarkovKernel (Q i)]
    {mu0 : Measure (State n × State n)} [IsProbabilityMeasure mu0]
    {V : Nat → (Fin k → Nat → State n × State n) → Real}
    {estimatorEps : Real}
    (hop : IndependentStreamOperational k (stateScheduleFromSeed Q) Q Prod.snd
      mu0 V (slowSourcePhases n N (slowSourceInitialVariance n) + 1) estimatorEps)
    (hmixError : ∀ j, hop.mixError j =
      activeReferenceMixError
        (slowSourcePhases n N (slowSourceInitialVariance n) + 2)
        (scoreAwareMixError
          (slowSourcePhases n N (slowSourceInitialVariance n) + 2) k (eps / 2)
          (fun t ↦ phaseMomentSlackSeven
            (slowSourcePhases n N (slowSourceInitialVariance n) + 1)
            (slowSourceSigmaSq n (slowSourceInitialVariance n)) K
            (fun _ ↦ 2) t / 6)
          (slowSharpBoundSq n R)) j)
    (htargetTV : ∀ j, TVLe (Measure.map Prod.fst (hop.tau j))
      (coolLaw (slowSourcePhases n N (slowSourceInitialVariance n) + 1)
        (slowSourceSigmaSq n (slowSourceInitialVariance n)) K j)
      (slowTargetError n
        (rAwareGlobalRadiusQ n R (slowSourceInitialVariance n)
          (slowUniformMeanTailFloor n
            (slowSourcePhases n N (slowSourceInitialVariance n) + 1) k eps R))
        (slowSourcePhases n N (slowSourceInitialVariance n) + 1) j)) :
    ∀ j, j ≤ slowSourcePhases n N (slowSourceInitialVariance n) + 1 →
      MemLp (positiveScalarPhaseFamilyChainLength (Seed := State n)
          (slowSourcePhases n N (slowSourceInitialVariance n) + 1)
          (slowSourceSigmaSq n (slowSourceInitialVariance n)) K j) 2
        (inhomogeneousPathMeasure (stateScheduleFromSeed Q) mu0) ∧
      ∫ omega,
          (positiveScalarPhaseFamilyChainLength (Seed := State n)
            (slowSourcePhases n N (slowSourceInitialVariance n) + 1)
            (slowSourceSigmaSq n (slowSourceInitialVariance n)) K j omega) ^ 2
          ∂(inhomogeneousPathMeasure (stateScheduleFromSeed Q) mu0) ≤
        7 * (∫ omega,
          positiveScalarPhaseFamilyChainLength (Seed := State n)
            (slowSourcePhases n N (slowSourceInitialVariance n) + 1)
            (slowSourceSigmaSq n (slowSourceInitialVariance n)) K j omega
          ∂(inhomogeneousPathMeasure (stateScheduleFromSeed Q) mu0)) ^ 2 := by
  have hn1 : 1 ≤ n := by omega
  have hs0 : 0 < slowSourceInitialVariance n := slowSourceInitialVariance_pos hn1
  exact operational_slowSource_positiveScalar_factorSeven_sharp_upto hn hN hs0 hsN hR2
    (slowUniformMeanTailFloor_pos heps) heps heps1 hK hKc hball hfin hKR hop
    hmixError htargetTV
    (slowSharp_htailBudget hn1
      (slowSourcePhases n N (slowSourceInitialVariance n) + 1) k hK hball hfin)

/-! ## The obstruction at the terminal index, recorded

The moment transport (`Arlib.GaussianCooling.sq_moment_le_of_tvLe`) consumes the score
bound `B` twice, in opposite directions: `∀ x, W x ≤ B` and
`ε · B^2 · (1 + 2T) ≤ s · ratio^2`.  Since the mixing budget delivers `ε · boundSq ≤ s`,
any usable `boundSq` must satisfy `boundSq ≥ B^2 · (1 + 2T)` with `B` an actual bound for
the score.  At the terminal index `B = exp (R^2/(2 σ_i))` *is* the true sup
(`Arlib.GaussianCooling.coolRatio_of_last` makes the ratio exactly `exp (‖x‖^2/(2 σ_i))`),
so there `B^2 · 15` is `phaseScoreTransportBoundSqSeven` itself: **no bound strictly below
the seven bound is usable at that one index.**  The equation below is that statement.
It is why the sharp package pays the mixing slack at `/6` rather than `/2`; the payment is
an absolute constant, and it buys the factor `n` in the exponent at every other index. -/
theorem terminal_sharpPhaseSup_sq_eq_seven
    {R : Real} {sigmaSq : Nat → Real} {m i : Nat} (hterm : m ≤ i + 1) :
    sharpPhaseSup n R sigmaSq m i ^ 2 * (1 + 2 * 7) =
      phaseScoreTransportBoundSqSeven R sigmaSq i := by
  unfold sharpPhaseSup phaseScoreTransportBoundSqSeven
  rw [if_neg (by omega)]

/-- The record in the other direction: at every **interior** index the sharpened bound is
attained exactly, `sup^2 · 15 = phaseScoreTransportBoundSqSharp`.  Together with
`Ttc.CVSharpScoreTransport.slowSharpBoundSq_le_slowUniformBoundSq` this is the whole
improvement: at `m - 1` of the `m` indices the transport multiplier drops from
`exp (R^2/(2 σ_i))^2 · 15` to `exp (R^2/(2 σ_i (n+1)))^2 · 15`. -/
theorem interior_sharpPhaseSup_sq_eq_sharp
    {R : Real} {sigmaSq : Nat → Real} {m i : Nat} (hint : i + 1 < m) :
    sharpPhaseSup n R sigmaSq m i ^ 2 * (1 + 2 * 7) =
      phaseScoreTransportBoundSqSharp n R sigmaSq i := by
  unfold sharpPhaseSup phaseScoreTransportBoundSqSharp
  rw [if_pos hint]

#print axioms sharpPhaseSup
#print axioms sharpPhaseSup_pos
#print axioms sharpPhaseSup_nonneg
#print axioms sharpPhaseSup_le_loose
#print axioms phaseScore_le_sharpPhaseSup
#print axioms abs_phaseScore_le_sharpPhaseSup
#print axioms phaseScore_sharp_le
#print axioms fifteen_le_phaseScoreTransportBoundSqSharp
#print axioms sharpPhaseSup_sq_mul_le_three_mul
#print axioms slowSharp_htailBudget
#print axioms phaseScore_interior_sq_moment_le_of_tvLe_bound
#print axioms operational_phaseScore_sq_moment_le_factor_bound
#print axioms operational_path_phaseScore_memLp_and_sq_moment_le_factor_of_targetTV_bound
#print axioms scoreAwareMix_add_slowTargetError_sharp_phaseBound_le
#print axioms operational_slowCanonical_phaseScore_factorSeven_sharp
#print axioms operational_slowCanonical_positiveScalar_factorSeven_sharp_upto
#print axioms operational_slowSource_positiveScalar_factorSeven_sharp_upto
#print axioms operational_slowCanonical_positiveScalar_factorSeven_sharpBound
#print axioms terminal_sharpPhaseSup_sq_eq_seven
#print axioms interior_sharpPhaseSup_sq_eq_sharp

end Ttc.CVSharpFactorSeven

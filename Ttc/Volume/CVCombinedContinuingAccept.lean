import Ttc.Volume.ContinuingRejectionSignificant
import Ttc.Volume.SpeedyAcceptanceRejection

/-! Combined shrink-membership and speedy-coin event for continuing rejection. -/

namespace Ttc.CVCombinedContinuingAccept

open MeasureTheory ProbabilityTheory Metric Set
open Arlib Arlib.MarkovChains
open Ttc.SpeedyRejection
open scoped ENNReal Pointwise

variable {n : Nat}
abbrev State (n : Nat) := EuclideanSpace Real (Fin n)

/-- Rescale a shrunken endpoint while retaining its speedy acceptance coin. -/
noncomputable def rescaleCoin (c : Real) (p : State n × Real) : State n × Real :=
  (c⁻¹ • p.1, p.2)

theorem measurable_rescaleCoin (c : Real) :
    Measurable (rescaleCoin (n := n) c) := by
  unfold rescaleCoin
  fun_prop

/-- A single candidate succeeds iff its endpoint lies in the shrunken body and its coin
accepts the rescaled endpoint.  On failure a continuing implementation keeps the raw
endpoint as its next chain state. -/
noncomputable def combinedAccept (K : Set (State n)) (c s : Real) : Set (State n × Real) :=
  Prod.fst ⁻¹' (c • K) ∩ rescaleCoin c ⁻¹' acceptRegion c s

theorem measurableSet_combinedAccept
    {K : Set (State n)} (hK : MeasurableSet K) {c s : Real} (hc : c ≠ 0) :
    MeasurableSet (combinedAccept K c s) := by
  exact (measurable_fst (measurableSet_smul_set hK hc)).inter
    ((measurableSet_acceptRegion c s).preimage (measurable_rescaleCoin c))

theorem mem_combinedAccept_iff
    (K : Set (State n)) (c s : Real) (p : State n × Real) :
    p ∈ combinedAccept K c s ↔
      p.1 ∈ c • K ∧ p.2 ≤ speedyAcceptReal c s (c⁻¹ • p.1) := by
  rfl

/-- Output map of a successful combined attempt. -/
noncomputable def combinedOutput (c : Real) (p : State n × Real) : State n := c⁻¹ • p.1

theorem measurable_combinedOutput (c : Real) :
    Measurable (combinedOutput (n := n) c) := by
  unfold combinedOutput
  fun_prop

/-- The raw endpoint retained by a rejected continuing attempt. -/
def combinedNext (p : State n × Real) : State n := p.1

theorem measurable_combinedNext : Measurable (combinedNext : State n × Real → State n) :=
  measurable_fst

theorem slice_combinedAccept_of_mem
    (K : Set (State n)) (c s : Real) {x : State n} (hx : x ∈ c • K) :
    Prod.mk x ⁻¹' combinedAccept K c s =
      Set.Iic (speedyAcceptReal c s (c⁻¹ • x)) := by
  ext u
  simp [combinedAccept, rescaleCoin, acceptRegion, hx]

theorem slice_combinedAccept_of_notMem
    (K : Set (State n)) (c s : Real) {x : State n} (hx : x ∉ c • K) :
    Prod.mk x ⁻¹' combinedAccept K c s = (∅ : Set Real) := by
  ext u
  simp [combinedAccept, rescaleCoin, acceptRegion, hx]

/-- Elementary mass identity behind the joint `1/8` bound. -/
theorem proposal_combinedAccept
    (Q : Measure (State n)) [IsProbabilityMeasure Q]
    {K : Set (State n)} (hK : MeasurableSet K) {c s : Real} (hc : c ≠ 0)
    (hs : 0 < s) (hc2 : c ^ 2 ≤ 1) :
    proposal Q (combinedAccept K c s) =
      ∫⁻ x in c • K,
        ENNReal.ofReal (speedyAcceptReal c s (c⁻¹ • x)) ∂Q := by
  rw [proposal, Measure.prod_apply (measurableSet_combinedAccept hK hc),
    ← lintegral_indicator (measurableSet_smul_set hK hc)]
  apply lintegral_congr
  intro x
  by_cases hx : x ∈ c • K
  · rw [Set.indicator_of_mem hx, slice_combinedAccept_of_mem K c s hx,
      unitCoin_Iic_speedyAccept hs hc2]
  · rw [Set.indicator_of_notMem hx, slice_combinedAccept_of_notMem K c s hx,
      measure_empty]

/-- Exact factorization into shrink mass and acceptance mass under the rescaled
shrink-conditioned proposal. -/
theorem proposal_combinedAccept_factor
    (Q : Measure (State n)) [IsProbabilityMeasure Q]
    {K : Set (State n)} (hK : MeasurableSet K) {c s : Real} (hc : c ≠ 0)
    (hs : 0 < s) (hc2 : c ^ 2 ≤ 1) (hshrink : Q (c • K) ≠ 0) :
    proposal Q (combinedAccept K c s) = Q (c • K) *
      (((Measure.map (fun x : State n => c⁻¹ • x) (Arlib.condOn Q (c • K))).withDensity
        (fun y => ENNReal.ofReal (speedyAcceptReal c s y))) Set.univ) := by
  have hmap :
      (∫⁻ y, ENNReal.ofReal (speedyAcceptReal c s y)
        ∂Measure.map (fun x : State n => c⁻¹ • x) (Arlib.condOn Q (c • K))) =
      ∫⁻ x, ENNReal.ofReal (speedyAcceptReal c s (c⁻¹ • x))
        ∂Arlib.condOn Q (c • K) := by
    exact lintegral_map
      (f := fun y : State n => ENNReal.ofReal (speedyAcceptReal c s y))
      (g := fun x : State n => c⁻¹ • x)
      (ENNReal.measurable_ofReal.comp (measurable_speedyAcceptReal c s))
      (measurable_const_smul _)
  rw [proposal_combinedAccept Q hK hc hs hc2,
    withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ, hmap,
    Arlib.condOn_def, lintegral_smul_measure]
  rw [← lintegral_indicator (measurableSet_smul_set hK hc)]
  simp only [smul_eq_mul]
  rw [← mul_assoc, ENNReal.mul_inv_cancel hshrink (measure_ne_top Q (c • K)), one_mul]

/-- Arithmetic lower bound for the combined event once its elementary mass factorization
has been established: half-mass shrink times quarter-mass speedy acceptance is `1/8`. -/
theorem combinedAcceptance_ge_eighth_of_factor
    {Q : Measure (State n × Real)} {K : Set (State n)} {c s : Real}
    {shrinkMass speedyMass : ENNReal}
    (hfactor : Q (combinedAccept K c s) = shrinkMass * speedyMass)
    (hhalf : ENNReal.ofReal (1 / 2 : Real) ≤ shrinkMass)
    (hquarter : ENNReal.ofReal (1 / 4 : Real) ≤ speedyMass) :
    ENNReal.ofReal (1 / 8 : Real) ≤ Q (combinedAccept K c s) := by
  rw [hfactor]
  calc
    ENNReal.ofReal (1 / 8 : Real) =
        ENNReal.ofReal (1 / 2 : Real) * ENNReal.ofReal (1 / 4 : Real) := by
      rw [← ENNReal.ofReal_mul (by norm_num)]
      norm_num
    _ ≤ shrinkMass * speedyMass := mul_le_mul hhalf hquarter (by simp) (by simp)

/-- The source's two acceptance estimates combine without any independence assumption:
the speedy quarter bound is taken under the rescaled shrink-conditioned proposal. -/
theorem proposal_combinedAccept_ge_eighth
    (Q : Measure (State n)) [IsProbabilityMeasure Q]
    {K : Set (State n)} (hK : MeasurableSet K) {c s : Real} (hc : c ≠ 0)
    (hs : 0 < s) (hc2 : c ^ 2 ≤ 1) (hshrink : Q (c • K) ≠ 0)
    (hhalf : ENNReal.ofReal (1 / 2 : Real) ≤ Q (c • K))
    (hquarter : ENNReal.ofReal (1 / 4 : Real) ≤
      (((Measure.map (fun x : State n => c⁻¹ • x) (Arlib.condOn Q (c • K))).withDensity
        (fun y => ENNReal.ofReal (speedyAcceptReal c s y))) Set.univ)) :
    ENNReal.ofReal (1 / 8 : Real) ≤ proposal Q (combinedAccept K c s) := by
  exact combinedAcceptance_ge_eighth_of_factor
    (proposal_combinedAccept_factor Q hK hc hs hc2 hshrink) hhalf hquarter

/-- One significant continuing retry, now for the actual combined shrink-membership and
speedy-coin event.  Lazy-speedy mixing is used only for the point candidate; tensoring the
same independent coin preserves its TV error.  The source's joint `1/8` acceptance lower
bound then costs the explicit factor `32` under conditioning. -/
theorem tvLe_combinedAccepted_at_distributionalWarmDeadline
    {H : Type*} [MeasurableSpace H]
    {rho : Measure H} [IsProbabilityMeasure rho]
    {pi tau : Measure (State n)} [IsProbabilityMeasure tau]
    (phase : Nat → Kernel (State n) (State n)) [∀ t : Nat, IsMarkovKernel (phase t)]
    (deadline : ENNReal → Nat)
    {last : H → State n} (hlast : Measurable last)
    {M eta zeta : ENNReal} (heta0 : eta ≠ 0)
    (hwarm : Arlib.IsWarm M (rho.map last) pi)
    {Survive : Set H} (hSurvive : MeasurableSet Survive)
    (hSurviveMass : eta ≤ rho Survive)
    (hmix : ∀ nu : Measure (State n),
      Arlib.IsWarm (M / eta) nu pi → IsProbabilityMeasure nu →
        Arlib.TVLe
          (Ttc.CVSequentialPhaseSampler.sampleFromKernel
            (phase (deadline (M / eta))) nu) tau zeta)
    {K : Set (State n)} (hK : MeasurableSet K) {c s : Real} (hc : c ≠ 0)
    (hs : 0 < s) (hc2 : c ^ 2 ≤ 1) (hshrink : tau (c • K) ≠ 0)
    (hhalf : ENNReal.ofReal (1 / 2 : Real) ≤ tau (c • K))
    (hquarter : ENNReal.ofReal (1 / 4 : Real) ≤
      (((Measure.map (fun x : State n => c⁻¹ • x) (Arlib.condOn tau (c • K))).withDensity
        (fun y => ENNReal.ofReal (speedyAcceptReal c s y))) Set.univ))
    (hzeta : zeta ≤ ENNReal.ofReal (1 / 16 : Real)) :
    let actual := Ttc.CVSequentialPhaseSampler.sampleFromKernel
      (phase (deadline (M / eta))) ((Arlib.condOn rho Survive).map last)
    Arlib.TVLe
      (Measure.map (combinedOutput c)
        (Arlib.condOn (proposal actual) (combinedAccept K c s)))
      (Measure.map (combinedOutput c)
        (Arlib.condOn (proposal tau) (combinedAccept K c s)))
      (32 * zeta) := by
  dsimp only
  have hS0 : rho Survive ≠ 0 := by
    intro hzero
    have : eta = 0 := le_antisymm (by simpa [hzero] using hSurviveMass) bot_le
    exact heta0 this
  letI : IsProbabilityMeasure (Arlib.condOn rho Survive) :=
    Arlib.isProbabilityMeasure_condOn rho hS0 (measure_ne_top rho Survive)
  letI : IsProbabilityMeasure ((Arlib.condOn rho Survive).map last) :=
    Measure.isProbabilityMeasure_map hlast.aemeasurable
  let actual := Ttc.CVSequentialPhaseSampler.sampleFromKernel
    (phase (deadline (M / eta))) ((Arlib.condOn rho Survive).map last)
  letI : IsProbabilityMeasure actual := by
    dsimp only [actual]
    infer_instance
  have hretry := Ttc.CVSignificantSurvivalWarm.tvLe_retry_at_distributionalWarmDeadline
    phase deadline hlast heta0 hwarm hSurvive hSurviveMass hmix
  have hpair : Arlib.TVLe (proposal actual) (proposal tau) zeta := by
    have hp := hretry.prod (Arlib.TVLe.refl unitCoin)
    simpa only [proposal, add_zero] using hp
  have heighth : ENNReal.ofReal (1 / 8 : Real) ≤
      proposal tau (combinedAccept K c s) :=
    proposal_combinedAccept_ge_eighth tau hK hc hs hc2 hshrink hhalf hquarter
  exact (Ttc.ContinuingRejectionSignificant.tvLe_condOn_eighth
    (proposal actual) (proposal tau) (measurableSet_combinedAccept hK hc)
    hpair heighth hzeta).map (measurable_combinedOutput c)

/-- Finite continuing-rejection capstone for an arbitrary event of ideal mass `1/8`.
The first-hit weights are the actual operational weights; only the unresolved cutoff branch
is charged as tail error. -/
theorem tvLe_continuingAcceptedMixture_eighth_of_survival
    {E : Type*} [MeasurableSpace E]
    (L : Nat) (w : Fin L → ENNReal) (candidate : Fin L → Measure E)
    [∀ i : Fin L, IsProbabilityMeasure (candidate i)]
    (tau : Measure E) [IsProbabilityMeasure tau]
    {A : Set E} (hA : MeasurableSet A)
    (survival : Nat → ENNReal) (eta r zeta : ENNReal) (fallback : E)
    (hmass : (∑ i, w i) + survival L = 1)
    (hcandidate : ∀ i, Arlib.TVLe (candidate i) tau zeta)
    (heighth : ENNReal.ofReal (1 / 8 : Real) ≤ tau A)
    (hzeta : zeta ≤ ENNReal.ofReal (1 / 16 : Real))
    (hs0 : survival 0 ≤ 1) (hr : r ≤ 1)
    (hmono : ∀ j, survival (j + 1) ≤ survival j)
    (hcontract : ∀ j, eta ≤ survival j → survival (j + 1) ≤ r * survival j) :
    Arlib.TVLe
      (Ttc.ContinuingRejectionSignificant.acceptedMixture L w
        (fun i ↦ Arlib.condOn (candidate i) A) (survival L) fallback)
      (Arlib.condOn tau A) (32 * zeta + (eta + r ^ L)) := by
  have htauPos : tau A ≠ 0 := ne_of_gt <|
    lt_of_lt_of_le (ENNReal.ofReal_pos.2 (by norm_num)) heighth
  letI : IsProbabilityMeasure (Arlib.condOn tau A) :=
    Arlib.isProbabilityMeasure_condOn _ htauPos (measure_ne_top tau A)
  have htail := Ttc.ContinuingRejectionSignificant.survival_le_eta_add_pow
    survival hs0 hr hmono hcontract L
  have hbase := Ttc.ContinuingRejectionSignificant.tvLe_acceptedMixture L w
    (fun i ↦ Arlib.condOn (candidate i) A) (Arlib.condOn tau A)
    (survival L) (32 * zeta) fallback hmass
    (fun i ↦ Ttc.ContinuingRejectionSignificant.tvLe_condOn_eighth
      (candidate i) tau hA (hcandidate i) heighth hzeta)
  exact hbase.mono (by gcongr)

#print axioms measurableSet_combinedAccept
#print axioms proposal_combinedAccept_factor
#print axioms proposal_combinedAccept_ge_eighth
#print axioms tvLe_combinedAccepted_at_distributionalWarmDeadline
#print axioms tvLe_continuingAcceptedMixture_eighth_of_survival
#print axioms combinedAcceptance_ge_eighth_of_factor

end Ttc.CVCombinedContinuingAccept

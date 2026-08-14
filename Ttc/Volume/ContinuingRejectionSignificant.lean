import Ttc.Volume.StatewiseNormalizationTV
import Ttc.Volume.AdaptiveRejectionTV
import Ttc.Volume.CVSignificantSurvivalWarm

/-! Finite continuing-chain rejection with a significant-survival split. -/

namespace Ttc.ContinuingRejectionSignificant

open MeasureTheory ProbabilityTheory Set
open Arlib
open scoped ENNReal BigOperators Classical

variable {E : Type*} [MeasurableSpace E]

/-- If a surviving branch contracts by `r` whenever it still has mass at least `eta`,
and otherwise can only decrease, then after `L` attempts its mass is at most
`eta + r^L`.  The small branch is charged only once. -/
theorem survival_le_eta_add_pow
    (s : Nat → ENNReal) {eta r : ENNReal}
    (hs0 : s 0 ≤ 1) (hr : r ≤ 1)
    (hmono : ∀ j, s (j + 1) ≤ s j)
    (hcontract : ∀ j, eta ≤ s j → s (j + 1) ≤ r * s j) :
    ∀ L, s L ≤ eta + r ^ L := by
  intro L
  induction L with
  | zero => simpa using hs0.trans (le_add_left le_rfl)
  | succ L ih =>
      by_cases hsig : eta ≤ s L
      · calc
          s (L + 1) ≤ r * s L := hcontract L hsig
          _ ≤ r * (eta + r ^ L) := mul_le_mul_left' ih r
          _ = r * eta + r ^ (L + 1) := by rw [mul_add, pow_succ']
          _ ≤ eta + r ^ (L + 1) := by
            gcongr
            exact (mul_le_of_le_one_left (by simp) hr)
      · have hsmall : s L ≤ eta := le_of_not_ge hsig
        exact (hmono L).trans <| hsmall.trans (le_add_right le_rfl)

/-- A finite mixture of accepted-output laws, plus a fallback carrying the entire
unresolved survival tail. -/
noncomputable def acceptedMixture (L : Nat) (w : Fin L → ENNReal)
    (q : Fin L → Measure E) (tail : ENNReal) (fallback : E) : Measure E :=
  (∑ i, w i • q i) + tail • Measure.dirac fallback

/-- Mixing laws that are all `delta`-close to the same target costs only `delta`, not
`L*delta`; the unresolved survival branch contributes its total mass once. -/
theorem tvLe_acceptedMixture
    (L : Nat) (w : Fin L → ENNReal) (q : Fin L → Measure E)
    (tau : Measure E) [IsProbabilityMeasure tau]
    (tail delta : ENNReal) (fallback : E)
    (hmass : (∑ i, w i) + tail = 1)
    (hq : ∀ i, TVLe (q i) tau delta) :
    TVLe (acceptedMixture L w q tail fallback) tau (delta + tail) := by
  intro S hS
  have hweights : ∑ i, w i ≤ 1 := by
    calc
      ∑ i, w i ≤ (∑ i, w i) + tail := le_add_right le_rfl
      _ = 1 := hmass
  have htau : tau S ≤ 1 := prob_le_one
  have hsumEval : (∑ i, w i • q i) S = ∑ i, w i * q i S := by
    simpa only [Measure.smul_apply, smul_eq_mul] using
      (Measure.finsetSum_apply Finset.univ (fun i => w i • q i) S)
  constructor
  · rw [acceptedMixture, Measure.add_apply, Measure.smul_apply,
      Measure.dirac_apply' _ hS, hsumEval]
    simp only [smul_eq_mul]
    have hsum : (∑ i, w i * q i S) ≤
        ∑ i, w i * (tau S + delta) :=
      Finset.sum_le_sum fun i _ => mul_le_mul_left' ((hq i).left hS) (w i)
    have hind : S.indicator (fun _ => (1 : ENNReal)) fallback ≤ 1 := by
      by_cases hf : fallback ∈ S <;> simp [Set.indicator_of_mem, Set.indicator_of_notMem, hf]
    have htailInd : tail * S.indicator 1 fallback ≤ tail := by
      by_cases hf : fallback ∈ S <;>
        simp [Set.indicator_of_mem, Set.indicator_of_notMem, hf]
    calc
      (∑ i, w i * q i S) + tail * S.indicator 1 fallback ≤
          (∑ i, w i * (tau S + delta)) + tail := by
        exact add_le_add hsum htailInd
      _ = (∑ i, w i) * tau S + (∑ i, w i) * delta + tail := by
        simp_rw [mul_add]
        rw [Finset.sum_add_distrib, Finset.sum_mul, Finset.sum_mul]
      _ ≤ tau S + delta + tail := by
        exact add_le_add (add_le_add
          (mul_le_of_le_one_left (by simp) hweights)
          (mul_le_of_le_one_left (by simp) hweights)) le_rfl
      _ ≤ tau S + (delta + tail) := by rw [add_assoc]
  · rw [acceptedMixture, Measure.add_apply, Measure.smul_apply,
      Measure.dirac_apply' _ hS, hsumEval]
    simp only [smul_eq_mul]
    have hweighted : (∑ i, w i) * tau S ≤
        (∑ i, w i * q i S) + (∑ i, w i) * delta := by
      calc
        (∑ i, w i) * tau S = ∑ i, w i * tau S := by rw [Finset.sum_mul]
        _ ≤ ∑ i, w i * (q i S + delta) := by
          exact Finset.sum_le_sum fun i _ =>
            mul_le_mul_left' ((hq i).right hS) (w i)
        _ = (∑ i, w i * q i S) + (∑ i, w i) * delta := by
          simp_rw [mul_add]
          rw [Finset.sum_add_distrib, Finset.sum_mul]
    calc
      tau S = ((∑ i, w i) + tail) * tau S := by rw [hmass, one_mul]
      _ = (∑ i, w i) * tau S + tail * tau S := by rw [add_mul]
      _ ≤ (∑ i, w i * q i S) + (∑ i, w i) * delta + tail := by
        exact add_le_add hweighted
          (mul_le_of_le_one_right (by simp) htau)
      _ ≤ ((∑ i, w i * q i S) + tail * S.indicator 1 fallback) +
          (delta + tail) := by
        calc
          _ ≤ (∑ i, w i * q i S) + delta + tail := by
            have hwdelta : (∑ i, w i) * delta ≤ delta :=
              mul_le_of_le_one_left (by simp) hweights
            calc
              _ = tail + ((∑ i, w i) * delta +
                  ∑ i, w i * q i S) := by ac_rfl
              _ ≤ tail + (delta + ∑ i, w i * q i S) := by
                have hin : (∑ i, w i) * delta + (∑ i, w i * q i S) ≤
                    delta + (∑ i, w i * q i S) := by
                  calc
                    _ = (∑ i, w i * q i S) + (∑ i, w i) * delta := add_comm _ _
                    _ ≤ (∑ i, w i * q i S) + delta := add_le_add_right hwdelta _
                    _ = _ := add_comm _ _
                exact add_le_add_right hin tail
              _ = _ := by ac_rfl
          _ ≤ ((∑ i, w i * q i S) + tail * S.indicator 1 fallback) +
              (delta + tail) := by
            calc
              _ ≤ ((∑ i, w i * q i S) + delta + tail) +
                  tail * S.indicator 1 fallback := le_add_right le_rfl
              _ = _ := by ac_rfl

/-- Conditioning a `zeta`-accurate proposal on a target event of mass at least `1/4`
costs at most `16*zeta`, provided `zeta ≤ 1/8`. -/
theorem tvLe_condOn_quarter
    (mu tau : Measure E) [IsProbabilityMeasure mu] [IsProbabilityMeasure tau]
    {A : Set E} (hA : MeasurableSet A) {zeta : ENNReal}
    (hTV : TVLe mu tau zeta)
    (hquarter : ENNReal.ofReal (1 / 4 : Real) ≤ tau A)
    (hzeta : zeta ≤ ENNReal.ofReal (1 / 8 : Real)) :
    TVLe (Arlib.condOn mu A) (Arlib.condOn tau A) (16 * zeta) := by
  have heighth : ENNReal.ofReal (1 / 8 : Real) ≤ mu A := by
    refine ENNReal.le_of_add_le_add_right
      (show ENNReal.ofReal (1 / 8 : Real) ≠ ⊤ from ENNReal.ofReal_ne_top) ?_
    calc
      ENNReal.ofReal (1 / 8 : Real) + ENNReal.ofReal (1 / 8 : Real) =
          ENNReal.ofReal (1 / 4 : Real) := by
        rw [← ENNReal.ofReal_add (by norm_num) (by norm_num)]
        norm_num
      _ ≤ tau A := hquarter
      _ ≤ mu A + zeta := hTV.right hA
      _ ≤ mu A + ENNReal.ofReal (1 / 8 : Real) := by gcongr
  have heighthTau : ENNReal.ofReal (1 / 8 : Real) ≤ tau A :=
    (ENNReal.ofReal_le_ofReal (by norm_num)).trans hquarter
  have hcond := hTV.condOn hA (m := ENNReal.ofReal (1 / 8 : Real))
    (ENNReal.ofReal_pos.2 (by norm_num)) heighth heighthTau
  have hconst : 2 * zeta / ENNReal.ofReal (1 / 8 : Real) = 16 * zeta := by
    have h8 : ENNReal.ofReal (1 / 8 : Real) = (8 : ENNReal)⁻¹ := by
      rw [show (1 / 8 : Real) = (8 : Real)⁻¹ by norm_num,
        ENNReal.ofReal_inv_of_pos (by norm_num)]
      norm_num
    rw [h8, ENNReal.div_eq_inv_mul, inv_inv]
    ring
  rwa [hconst] at hcond

/-- Arbitrary-mass form: if the target accepts with mass at least `2*m` and the proposal
error is at most `m`, conditioning costs `2*zeta/m`. -/
theorem tvLe_condOn_of_two_mul_mass
    (mu tau : Measure E) [IsProbabilityMeasure mu] [IsProbabilityMeasure tau]
    {A : Set E} (hA : MeasurableSet A) {zeta m : ENNReal}
    (hTV : TVLe mu tau zeta) (hm : 0 < m) (hmtop : m ≠ ⊤)
    (htarget : 2 * m ≤ tau A) (hzeta : zeta ≤ m) :
    TVLe (Arlib.condOn mu A) (Arlib.condOn tau A) (2 * zeta / m) := by
  have hmu : m ≤ mu A := by
    refine ENNReal.le_of_add_le_add_right hmtop ?_
    calc
      m + m = 2 * m := by ring
      _ ≤ tau A := htarget
      _ ≤ mu A + zeta := hTV.right hA
      _ ≤ mu A + m := by gcongr
  have htau : m ≤ tau A :=
    le_trans (by rw [two_mul]; exact le_add_right le_rfl) htarget
  exact hTV.condOn hA hm hmu htau

/-- Joint shrink-and-speedy acceptance has source lower bound `1/8`; with
`zeta ≤ 1/16`, conditioning therefore costs `32*zeta`. -/
theorem tvLe_condOn_eighth
    (mu tau : Measure E) [IsProbabilityMeasure mu] [IsProbabilityMeasure tau]
    {A : Set E} (hA : MeasurableSet A) {zeta : ENNReal}
    (hTV : TVLe mu tau zeta)
    (heighth : ENNReal.ofReal (1 / 8 : Real) ≤ tau A)
    (hzeta : zeta ≤ ENNReal.ofReal (1 / 16 : Real)) :
    TVLe (Arlib.condOn mu A) (Arlib.condOn tau A) (32 * zeta) := by
  have hbase := tvLe_condOn_of_two_mul_mass mu tau hA hTV
    (m := ENNReal.ofReal (1 / 16 : Real))
    (ENNReal.ofReal_pos.2 (by norm_num)) ENNReal.ofReal_ne_top
    (by
      calc
        2 * ENNReal.ofReal (1 / 16 : Real) =
            ENNReal.ofReal (1 / 8 : Real) := by
          rw [← ENNReal.ofReal_ofNat, ← ENNReal.ofReal_mul (by norm_num)]
          norm_num
        _ ≤ tau A := heighth)
    hzeta
  have hconst : 2 * zeta / ENNReal.ofReal (1 / 16 : Real) = 32 * zeta := by
    have h16 : ENNReal.ofReal (1 / 16 : Real) = (16 : ENNReal)⁻¹ := by
      rw [show (1 / 16 : Real) = (16 : Real)⁻¹ by norm_num,
        ENNReal.ofReal_inv_of_pos (by norm_num)]
      norm_num
    rw [h16, ENNReal.div_eq_inv_mul, inv_inv]
    ring
  rwa [hconst] at hbase

/-- One significant continuing retry, specialized to the CV distributional-warm deadline:
mix from the survival-conditioned last state, then perform one quarter-mass rejection
normalization. -/
theorem tvLe_retryAccepted_at_distributionalWarmDeadline_quarter
    {H X : Type*} [MeasurableSpace H] [MeasurableSpace X]
    {rho : Measure H} [IsProbabilityMeasure rho]
    {pi tau : Measure X} [IsProbabilityMeasure tau]
    (phase : Nat → Kernel X X) [∀ t, IsMarkovKernel (phase t)]
    (deadline : ENNReal → Nat)
    {last : H → X} (hlast : Measurable last)
    {M eta zeta : ENNReal} (heta0 : eta ≠ 0)
    (hwarm : Arlib.IsWarm M (rho.map last) pi)
    {Survive : Set H} (hSurvive : MeasurableSet Survive)
    (hSurviveMass : eta ≤ rho Survive)
    (hmix : ∀ nu : Measure X,
      Arlib.IsWarm (M / eta) nu pi → IsProbabilityMeasure nu →
        TVLe
          (Ttc.CVSequentialPhaseSampler.sampleFromKernel
            (phase (deadline (M / eta))) nu) tau zeta)
    {Accept : Set X} (hAccept : MeasurableSet Accept)
    (hquarter : ENNReal.ofReal (1 / 4 : Real) ≤ tau Accept)
    (hzeta : zeta ≤ ENNReal.ofReal (1 / 8 : Real)) :
    TVLe
      (Arlib.condOn
        (Ttc.CVSequentialPhaseSampler.sampleFromKernel
          (phase (deadline (M / eta))) ((Arlib.condOn rho Survive).map last)) Accept)
      (Arlib.condOn tau Accept) (16 * zeta) := by
  have hS0 : rho Survive ≠ 0 := by
    intro hzero
    have : eta = 0 := le_antisymm (by simpa [hzero] using hSurviveMass) bot_le
    exact heta0 this
  letI : IsProbabilityMeasure (Arlib.condOn rho Survive) :=
    Arlib.isProbabilityMeasure_condOn rho hS0 (measure_ne_top rho Survive)
  letI : IsProbabilityMeasure ((Arlib.condOn rho Survive).map last) :=
    Measure.isProbabilityMeasure_map hlast.aemeasurable
  letI : IsProbabilityMeasure
      (Ttc.CVSequentialPhaseSampler.sampleFromKernel
        (phase (deadline (M / eta))) ((Arlib.condOn rho Survive).map last)) := by
    unfold Ttc.CVSequentialPhaseSampler.sampleFromKernel
    infer_instance
  have hretry := Ttc.CVSignificantSurvivalWarm.tvLe_retry_at_distributionalWarmDeadline
    phase deadline hlast heta0 hwarm hSurvive hSurviveMass hmix
  exact tvLe_condOn_quarter _ tau hAccept hretry hquarter hzeta

/-- Generic finite continuing-rejection capstone.  Accepted attempts are mixed with their
actual first-hit weights; the unresolved branch is charged once. -/
theorem tvLe_continuingAcceptedMixture_quarter
    (L : Nat) (w : Fin L → ENNReal) (proposal : Fin L → Measure E)
    [∀ i, IsProbabilityMeasure (proposal i)]
    (tau : Measure E) [IsProbabilityMeasure tau]
    {A : Set E} (hA : MeasurableSet A)
    (tail eta r zeta : ENNReal) (fallback : E)
    (hmass : (∑ i, w i) + tail = 1)
    (hproposal : ∀ i, TVLe (proposal i) tau zeta)
    (hquarter : ENNReal.ofReal (1 / 4 : Real) ≤ tau A)
    (hzeta : zeta ≤ ENNReal.ofReal (1 / 8 : Real))
    (htail : tail ≤ eta + r ^ L) :
    TVLe
      (acceptedMixture L w (fun i => Arlib.condOn (proposal i) A) tail fallback)
      (Arlib.condOn tau A) (16 * zeta + (eta + r ^ L)) := by
  have htauPos : tau A ≠ 0 := ne_of_gt <|
    lt_of_lt_of_le (ENNReal.ofReal_pos.2 (by norm_num)) hquarter
  letI : IsProbabilityMeasure (Arlib.condOn tau A) :=
    Arlib.isProbabilityMeasure_condOn _ htauPos (measure_ne_top tau A)
  have hbase := tvLe_acceptedMixture L w
    (fun i => Arlib.condOn (proposal i) A) (Arlib.condOn tau A)
    tail (16 * zeta) fallback hmass
    (fun i => tvLe_condOn_quarter (proposal i) tau hA
      (hproposal i) hquarter hzeta)
  exact hbase.mono (by gcongr)

/-- The preceding capstone with its tail discharged by the significant-survival
contraction recurrence. -/
theorem tvLe_continuingAcceptedMixture_quarter_of_survival
    (L : Nat) (w : Fin L → ENNReal) (proposal : Fin L → Measure E)
    [∀ i, IsProbabilityMeasure (proposal i)]
    (tau : Measure E) [IsProbabilityMeasure tau]
    {A : Set E} (hA : MeasurableSet A)
    (s : Nat → ENNReal) (eta r zeta : ENNReal) (fallback : E)
    (hmass : (∑ i, w i) + s L = 1)
    (hproposal : ∀ i, TVLe (proposal i) tau zeta)
    (hquarter : ENNReal.ofReal (1 / 4 : Real) ≤ tau A)
    (hzeta : zeta ≤ ENNReal.ofReal (1 / 8 : Real))
    (hs0 : s 0 ≤ 1) (hr : r ≤ 1)
    (hmono : ∀ j, s (j + 1) ≤ s j)
    (hcontract : ∀ j, eta ≤ s j → s (j + 1) ≤ r * s j) :
    TVLe
      (acceptedMixture L w (fun i => Arlib.condOn (proposal i) A) (s L) fallback)
      (Arlib.condOn tau A) (16 * zeta + (eta + r ^ L)) := by
  apply tvLe_continuingAcceptedMixture_quarter L w proposal tau hA
    (s L) eta r zeta fallback hmass hproposal hquarter hzeta
  exact survival_le_eta_add_pow s hs0 hr hmono hcontract L

#print axioms survival_le_eta_add_pow
#print axioms tvLe_acceptedMixture
#print axioms tvLe_condOn_quarter
#print axioms tvLe_condOn_of_two_mul_mass
#print axioms tvLe_condOn_eighth
#print axioms tvLe_retryAccepted_at_distributionalWarmDeadline_quarter
#print axioms tvLe_continuingAcceptedMixture_quarter
#print axioms tvLe_continuingAcceptedMixture_quarter_of_survival

end Ttc.ContinuingRejectionSignificant

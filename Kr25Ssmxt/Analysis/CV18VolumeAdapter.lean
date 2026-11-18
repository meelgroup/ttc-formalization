import Kr25Ssmxt.Analysis.OracleContracts
import Kr25Ssmxt.Analysis.MathlibCompat
import Kr25Ssmxt.Analysis.CV18NormalizedPolytope
import Kr25Ssmxt.Analysis.ReferenceProgram

/-!
# Adapting a normalized CV18 volume law to TTC

CV18 runs on `P.cv18Body`, while TTC reports the volume of `P.carrier`.  This file rescales
the estimator output by `inradius^n` and transports probability, failure, and relative-error
guarantees through that deterministic map.
-/

noncomputable section

open MeasureTheory
open scoped ENNReal NNReal ProbabilityTheory

namespace Kr25Ssmxt

/-! ## Turning a high-probability estimator event into TTC's tagged law -/

/-- Boolean tag of membership in an arbitrary set. -/
noncomputable def volumeSuccessTag {Omega : Type*} (good : Set Omega) (omega : Omega) : Bool := by
  classical
  exact if omega ∈ good then true else false

@[simp] lemma volumeSuccessTag_eq_true_iff {Omega : Type*} (good : Set Omega) (omega : Omega) :
    volumeSuccessTag good omega = true ↔ omega ∈ good := by
  classical
  simp [volumeSuccessTag]

@[simp] lemma volumeSuccessTag_eq_false_iff {Omega : Type*} (good : Set Omega) (omega : Omega) :
    volumeSuccessTag good omega = false ↔ omega ∉ good := by
  classical
  simp [volumeSuccessTag]

/-- Tag an estimator output by membership in a measurable success event.  This is the
measure-level adapter between CV18's lower bound on a success set and TTC's convention that
all inaccurate outputs carry the `false` tag. -/
noncomputable def taggedVolumeLaw {Omega : Type*} [MeasurableSpace Omega]
    (mu : Measure Omega) (good : Set Omega) (estimate : Omega -> NNReal) :
    Measure VolumeOutcome := by
  exact mu.map fun omega => (volumeSuccessTag good omega, estimate omega)

lemma measurable_taggedVolumeOutcome {Omega : Type*} [MeasurableSpace Omega]
    {good : Set Omega} (hgood : MeasurableSet good)
    {estimate : Omega -> NNReal} (hestimate : Measurable estimate) :
    Measurable fun omega => (volumeSuccessTag good omega, estimate omega) := by
  classical
  have htag : Measurable (volumeSuccessTag good) := by
    unfold volumeSuccessTag
    exact Measurable.ite hgood measurable_const measurable_const
  exact htag.prodMk hestimate

/-- Any measurable high-probability relative-accuracy event becomes a TTC volume law with
the same failure budget.  No sampling or CV18 mathematics is hidden here: callers supply the
event-probability theorem and the pointwise meaning of that event. -/
theorem taggedVolumeLaw_spec {Omega : Type*} [MeasurableSpace Omega]
    (mu : Measure Omega) [IsProbabilityMeasure mu]
    {good : Set Omega} (hgood : MeasurableSet good)
    {estimate : Omega -> NNReal} (hestimate : Measurable estimate)
    {target eta delta : Real}
    (hsuccess : 1 - delta <= mu.real good)
    (haccuracy : forall omega, omega ∈ good ->
      (estimate omega : Real) ∈ Arlib.relErr eta target) :
    IsProbabilityMeasure (taggedVolumeLaw mu good estimate) ∧
      (taggedVolumeLaw mu good estimate).real {o | o.1 = false} <= delta ∧
      ∀ᵐ o ∂taggedVolumeLaw mu good estimate, o.1 = true ->
        (o.2 : Real) ∈ Arlib.relErr eta target := by
  classical
  let out : Omega -> VolumeOutcome :=
    fun omega => (volumeSuccessTag good omega, estimate omega)
  have hout : Measurable out :=
    measurable_taggedVolumeOutcome hgood hestimate
  have hpreFalse : out ⁻¹' {o : VolumeOutcome | o.1 = false} = goodᶜ := by
    ext omega
    simp [out]
  constructor
  · unfold taggedVolumeLaw
    exact Measure.isProbabilityMeasure_map hout.aemeasurable
  constructor
  · change (mu.map out).real {o : VolumeOutcome | o.1 = false} <= delta
    rw [Measure.real, Measure.map_apply hout (by measurability), hpreFalse,
      ← Measure.real, probReal_compl_eq_one_sub hgood]
    linarith
  · unfold taggedVolumeLaw
    rw [MeasureTheory.ae_map_iff hout.aemeasurable (by measurability)]
    filter_upwards with omega
    intro htag
    have homega : omega ∈ good := by
      simpa [out] using htag
    simpa [out, homega] using haccuracy omega homega

lemma PolytopeData.measurable_rescaleCV18Outcome {n : Nat} (P : PolytopeData n) :
    Measurable P.rescaleCV18Outcome := by
  unfold PolytopeData.rescaleCV18Outcome
  fun_prop

/-- The exact adapter theorem needed by a CV18 implementation: a normalized-body law with
the usual contract yields TTC's volume law at the same accuracy and failure probability. -/
theorem PolytopeData.rescaleCV18Law_spec {n : Nat} (P : PolytopeData n)
    (mu : Measure VolumeOutcome) [IsProbabilityMeasure mu]
    {eta delta : Real}
    (hfail : mu.real {o | o.1 = false} ≤ delta)
    (hacc : ∀ᵐ o ∂mu, o.1 = true →
      (o.2 : Real) ∈ Arlib.relErr eta (volume P.cv18Body).toReal) :
    IsProbabilityMeasure (P.rescaleCV18Law mu) ∧
      (P.rescaleCV18Law mu).real {o | o.1 = false} ≤ delta ∧
      ∀ᵐ o ∂P.rescaleCV18Law mu, o.1 = true →
        (o.2 : Real) ∈ Arlib.relErr eta (volume P.carrier).toReal := by
  have hmap : Measurable P.rescaleCV18Outcome := P.measurable_rescaleCV18Outcome
  refine ⟨Measure.isProbabilityMeasure_map hmap.aemeasurable, ?_, ?_⟩
  · rw [PolytopeData.rescaleCV18Law, Measure.real, Measure.map_apply hmap (by measurability)]
    simpa [Measure.real, PolytopeData.rescaleCV18Outcome] using hfail
  · rw [PolytopeData.rescaleCV18Law,
      MeasureTheory.ae_map_iff hmap.aemeasurable (by measurability)]
    filter_upwards [hacc] with o ho
    intro htag
    have ho' := ho htag
    have hc : 0 ≤ P.inradius ^ n := pow_nonneg P.inradius_pos.le n
    have htarget := P.inradiusPow_mul_volume_cv18Body_toReal
    change P.inradius ^ n * (o.2 : Real) ∈
      Arlib.relErr eta (volume P.carrier).toReal
    rw [← htarget, Arlib.mem_relErr] at ⊢
    rw [Arlib.mem_relErr] at ho'
    constructor
    · calc
        (1 - eta) * (P.inradius ^ n * (volume P.cv18Body).toReal) =
            P.inradius ^ n * ((1 - eta) * (volume P.cv18Body).toReal) := by ring
        _ ≤ P.inradius ^ n * (o.2 : Real) :=
          mul_le_mul_of_nonneg_left ho'.1 hc
    · calc
        P.inradius ^ n * (o.2 : Real) ≤
            P.inradius ^ n * ((1 + eta) * (volume P.cv18Body).toReal) :=
          mul_le_mul_of_nonneg_left ho'.2 hc
        _ = (1 + eta) * (P.inradius ^ n * (volume P.cv18Body).toReal) := by ring

/-- Direct composition for a normalized CV18 estimator: tag its proved success event, then
rescale its estimate back to TTC coordinates.  This is the exact adapter consumed by a future
`ComputeVolume` implementation based on the costed Arlib CV18 capstone. -/
theorem PolytopeData.rescaleTaggedVolumeLaw_spec {n : Nat} (P : PolytopeData n)
    {Omega : Type*} [MeasurableSpace Omega]
    (mu : Measure Omega) [IsProbabilityMeasure mu]
    {good : Set Omega} (hgood : MeasurableSet good)
    {estimate : Omega -> NNReal} (hestimate : Measurable estimate)
    {eta delta : Real}
    (hsuccess : 1 - delta <= mu.real good)
    (haccuracy : forall omega, omega ∈ good ->
      (estimate omega : Real) ∈ Arlib.relErr eta (volume P.cv18Body).toReal) :
    IsProbabilityMeasure
        (P.rescaleCV18Law (taggedVolumeLaw mu good estimate)) ∧
      (P.rescaleCV18Law (taggedVolumeLaw mu good estimate)).real
          {o | o.1 = false} <= delta ∧
      ∀ᵐ o ∂P.rescaleCV18Law (taggedVolumeLaw mu good estimate), o.1 = true ->
        (o.2 : Real) ∈ Arlib.relErr eta (volume P.carrier).toReal := by
  have htag := taggedVolumeLaw_spec mu hgood hestimate hsuccess haccuracy
  letI : IsProbabilityMeasure (taggedVolumeLaw mu good estimate) := htag.1
  exact P.rescaleCV18Law_spec (taggedVolumeLaw mu good estimate) htag.2.1 htag.2.2

/-! ## Installing a normalized CV18 provider in TTC -/

/-- Parameter regime in which a probabilistic relative-volume request is meaningful and
which contains every call made by TTC.  Stating this condition is necessary: a requirement
that failure probability be at most an arbitrary real `delta` would include negative
`delta` and hence make the provider interface uninhabited. -/
def AdmissibleCV18Request (eta delta : Real) : Prop :=
  0 < eta ∧ eta <= 1 ∧ 0 < delta ∧ delta <= 1

/-- Contract of a volume implementation on TTC's normalized body.  The provider may be
instantiated by a tagged costed-CV18 estimator law; this interface contains no semantic exact
volume oracle. -/
structure NormalizedCV18VolumeProvider (n : Nat) where
  law : PolytopeData n -> Real -> Real -> Measure VolumeOutcome
  probability : forall P eta delta, IsProbabilityMeasure (law P eta delta)
  failure : forall P eta delta, AdmissibleCV18Request eta delta ->
    (law P eta delta).real {o | o.1 = false} <= delta
  accuracy : forall P eta delta, AdmissibleCV18Request eta delta ->
    ∀ᵐ o ∂law P eta delta, o.1 = true ->
      (o.2 : Real) ∈ Arlib.relErr eta (volume P.cv18Body).toReal

/-- Build a total provider from an implementation defined only on meaningful requests.
Outside that regime the law is an arbitrary probability measure; TTC never uses its
accuracy or failure properties there. -/
noncomputable def NormalizedCV18VolumeProvider.ofAdmissible {n : Nat}
    (validLaw : forall (P : PolytopeData n) (eta delta : Real),
      AdmissibleCV18Request eta delta -> Measure VolumeOutcome)
    (hprob : forall P eta delta h,
      IsProbabilityMeasure (validLaw P eta delta h))
    (hfail : forall P eta delta h,
      (validLaw P eta delta h).real {o | o.1 = false} <= delta)
    (hacc : forall P eta delta h,
      ∀ᵐ o ∂validLaw P eta delta h, o.1 = true ->
        (o.2 : Real) ∈ Arlib.relErr eta (volume P.cv18Body).toReal) :
    NormalizedCV18VolumeProvider n := by
  classical
  exact
    { law := fun P eta delta => if h : AdmissibleCV18Request eta delta then
        validLaw P eta delta h else Measure.dirac (true, 0)
      probability := fun P eta delta => by
        split_ifs with h
        · exact hprob P eta delta h
        · infer_instance
      failure := fun P eta delta h => by
        simp only [dif_pos h]
        exact hfail P eta delta h
      accuracy := fun P eta delta h => by
        simp only [dif_pos h]
        exact hacc P eta delta h }

/-- Replace only the volume field of an oracle bundle by a normalized CV18 provider. -/
def TTCOracles.withNormalizedCV18Volume {n k : Nat} (O : TTCOracles n k)
    (V : NormalizedCV18VolumeProvider n) : TTCOracles n k :=
  { O with
    ComputeVolume := fun P eta delta => P.rescaleCV18Law (V.law P eta delta) }

/-- A normalized CV18 provider discharges TTC's volume contract after the proved affine
rescaling of each preprocessed component. -/
theorem withNormalizedCV18Volume_volume_contract {n k : Nat}
    (O : TTCOracles n k) (V : NormalizedCV18VolumeProvider n)
    (F : LRAFormula n k) (hbounded : Bornology.IsBounded (solutionSet F))
    (params : ApproxParams) :
    ComputeVolumeContract (O.withNormalizedCV18Volume V) F hbounded params := by
  let D := O.preprocessing.run F hbounded
  intro i
  let P := D.component i
  let eta := params.ε'
  let delta := params.δ' D.componentCount
  have hcount : 0 < D.componentCount := lt_of_le_of_lt (Nat.zero_le i) i.isLt
  have heta0 : 0 < eta := by
    dsimp only [eta, ApproxParams.ε']
    exact div_pos params.epsilon_pos (by norm_num)
  have heta1 : eta <= 1 := by
    dsimp only [eta, ApproxParams.ε']
    linarith [params.epsilon_le_one]
  have hdenom : 0 < (4 * D.componentCount : Real) := by
    exact_mod_cast Nat.mul_pos (by norm_num : 0 < 4) hcount
  have hdelta0 : 0 < delta := by
    dsimp only [delta, ApproxParams.δ']
    exact div_pos params.delta_pos hdenom
  have hdelta1 : delta <= 1 := by
    dsimp only [delta, ApproxParams.δ']
    rw [div_le_iff₀ hdenom]
    have hcountR : (1 : Real) <= D.componentCount := by exact_mod_cast hcount
    nlinarith [params.delta_le_one]
  have hrequest : AdmissibleCV18Request eta delta :=
    ⟨heta0, heta1, hdelta0, hdelta1⟩
  letI : IsProbabilityMeasure (V.law P eta delta) := V.probability P eta delta
  simpa only [TTCOracles.withNormalizedCV18Volume, D, P, eta, delta] using
    P.rescaleCV18Law_spec (V.law P eta delta)
      (V.failure P eta delta hrequest) (V.accuracy P eta delta hrequest)

#print axioms taggedVolumeLaw_spec
#print axioms PolytopeData.rescaleTaggedVolumeLaw_spec
#print axioms withNormalizedCV18Volume_volume_contract

end Kr25Ssmxt

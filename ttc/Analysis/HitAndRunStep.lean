import ttc.Analysis.MembershipCost
import ttc.Analysis.GaussianDirection

/-! # The Hit-and-Run step program is arlib's lazy Hit-and-Run kernel

`HalfspacePresentation.hitAndRunStep` (`Model/Prelude.lean`) is a program over unit-cost
operations driven by a random tape. This file proves:

* what it computes: the chord scan returns arlib's endpoints `lower`/`upper`, and
  `normalize g` is `g/‖g‖`;
* that the law of its output, over the tape `hitAndRunTape`, is arlib's lazy finite-facet
  Hit-and-Run kernel at every point of the body;
* that `T` steps from a start law on the body have the law of arlib's `T`-step chain. -/

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal InnerProductSpace

namespace ttc

open ArlibCommunity.Foundations.MarkovChainTheory.PolytopeChord

namespace HitAndRunProg

/-- `⨆` over `Fin (r + 1)` splits off the first index. -/
theorem iSup_fin_succ {α : Type*} [CompleteLinearOrder α] {r : Nat} (f : Fin (r + 1) → α) :
    ⨆ i, f i = max (f 0) (⨆ i : Fin r, f i.succ) := by
  refine le_antisymm (iSup_le fun i => Fin.cases (le_max_left _ _)
    (fun j => le_max_of_le_right (le_iSup (fun k : Fin r => f k.succ) j)) i) ?_
  exact max_le (le_iSup f 0) (iSup_le fun i => le_iSup f i.succ)

/-- `⨅` over `Fin (r + 1)` splits off the first index. -/
theorem iInf_fin_succ {α : Type*} [CompleteLinearOrder α] {r : Nat} (f : Fin (r + 1) → α) :
    ⨅ i, f i = min (f 0) (⨅ i : Fin r, f i.succ) :=
  iSup_fin_succ (α := αᵒᵈ) f

/-- The facet normals as arlib vectors. -/
def arlibNormals {n r : Nat} (a : Fin r → Fin n → Real) : Fin r → EuclideanSpace Real (Fin n) :=
  fun j => toEuclidean (a j)

theorem coeff_eq {n r : Nat} (a : Fin r → Fin n → Real) (θ : Fin n → Real) (j : Fin r) :
    coeff (arlibNormals a) (WithLp.toLp 2 θ) j = dotProduct (a j) θ := by
  simp [coeff, arlibNormals, inner_toEuclidean]

theorem slack_eq {n r : Nat} (a : Fin r → Fin n → Real) (β : Fin r → Real)
    (x : Fin n → Real) (j : Fin r) :
    slack (arlibNormals a) β (WithLp.toLp 2 x) j = β j - dotProduct (a j) x := by
  simp [slack, arlibNormals, inner_toEuclidean]

open Classical in
/-- One facet's endpoints are arlib's endpoint candidates. -/
theorem facetEndpoints_value {n r : Nat} (a : Fin r → Fin n → Real) (β : Fin r → Real)
    (x θ : Fin n → Real) (j : Fin r) :
    (facetEndpoints n (a j) (β j) x θ).value =
      (lowerCandidate (arlibNormals a) β (WithLp.toLp 2 x) (WithLp.toLp 2 θ) j,
        upperCandidate (arlibNormals a) β (WithLp.toLp 2 x) (WithLp.toLp 2 θ) j) := by
  simp only [facetEndpoints, Counted.bind_eq, Counted.andThen_value, Counted.pure_value,
    Counted.dot_value, Counted.sub, Counted.div, Counted.lt, lowerCandidate, upperCandidate,
    ratio, coeff_eq, slack_eq, decide_eq_true_eq]

/-- **The chord scan computes arlib's extended endpoints.** -/
theorem chord_value {n : Nat} : ∀ (r : Nat) (a : Fin r → Fin n → Real) (β : Fin r → Real)
    (x θ : Fin n → Real),
    (chord n r a β x θ).value =
      (lowerE (arlibNormals a) β (WithLp.toLp 2 x) (WithLp.toLp 2 θ),
        upperE (arlibNormals a) β (WithLp.toLp 2 x) (WithLp.toLp 2 θ))
  | 0, a, β, x, θ => by simp [chord, lowerE, upperE]
  | r + 1, a, β, x, θ => by
      simp only [chord, Counted.bind_eq, Counted.andThen_value, Counted.pure_value,
        Counted.maxE, Counted.minE, chord_value r, facetEndpoints_value a β x θ 0]
      simp only [lowerE, upperE, iSup_fin_succ (lowerCandidate _ _ _ _),
        iInf_fin_succ (upperCandidate _ _ _ _)]
      rfl

/-- **`normalize` computes `g/‖g‖`** (and `0` at `g = 0`). -/
theorem normalize_value {n : Nat} (g : Fin n → Real) :
    WithLp.toLp 2 (normalize n g).value = ‖WithLp.toLp 2 g‖⁻¹ • WithLp.toLp 2 g := by
  have hnorm : ‖(WithLp.toLp 2 g : EuclideanSpace Real (Fin n))‖ =
      Real.sqrt (dotProduct g g) := by
    rw [EuclideanSpace.norm_eq]
    simp [dotProduct, sq]
  ext i
  simp [normalize, Counted.forEach, Counted.mul, Counted.div, Counted.sqrt, Counted.dot_value,
    hnorm]

end HitAndRunProg

open HitAndRunProg

/-- The walk's lower chord endpoint from `x` in direction `θ`, in arlib's terms. -/
noncomputable abbrev HalfspacePresentation.lo {n : Nat} (H : HalfspacePresentation n)
    (x θ : EuclideanSpace Real (Fin n)) : Real :=
  lower (arlibNormals H.normal) H.offset x θ

/-- The walk's upper chord endpoint. -/
noncomputable abbrev HalfspacePresentation.hi {n : Nat} (H : HalfspacePresentation n)
    (x θ : EuclideanSpace Real (Fin n)) : Real :=
  upper (arlibNormals H.normal) H.offset x θ

/-- The move of a non-lazy step: along the direction of `g`, to the point at fraction `u` of
the chord, or stay put if the chord is degenerate. -/
noncomputable def HalfspacePresentation.move {n : Nat} (H : HalfspacePresentation n)
    (x g : EuclideanSpace Real (Fin n)) (u : Real) : EuclideanSpace Real (Fin n) :=
  let θ := ‖g‖⁻¹ • g
  if H.lo x θ < H.hi x θ then x + (H.lo x θ + u * (H.hi x θ - H.lo x θ)) • θ else x

/-- **What one step computes.** -/
theorem HalfspacePresentation.hitAndRunStep_value {n : Nat} (H : HalfspacePresentation n)
    (x : EuclideanSpace Real (Fin n)) (coin : Bool) (g : EuclideanSpace Real (Fin n))
    (u : Real) :
    WithLp.toLp 2 (H.hitAndRunStep (WithLp.ofLp x) coin (WithLp.ofLp g) u).value =
      if coin then x else H.move x g u := by
  have hθ := normalize_value (WithLp.ofLp g)
  simp only [WithLp.toLp_ofLp] at hθ
  cases coin
  · simp only [HalfspacePresentation.hitAndRunStep, Counted.bind_eq, Counted.andThen_value,
      Counted.draw, Bool.false_eq_true, ite_false, chord_value, Counted.toReal, Counted.lt,
      WithLp.toLp_ofLp, hθ, HalfspacePresentation.move]
    have hθi : ∀ i, (normalize n (WithLp.ofLp g)).value i = ‖g‖⁻¹ * g i := fun i => by
      simpa using congrArg (fun v : EuclideanSpace Real (Fin n) => v i) hθ
    simp only [HalfspacePresentation.lo, HalfspacePresentation.hi, lower, upper,
      decide_eq_true_eq]
    by_cases h : (lowerE (arlibNormals H.normal) H.offset x (‖g‖⁻¹ • g)).toReal <
        (upperE (arlibNormals H.normal) H.offset x (‖g‖⁻¹ • g)).toReal
    · simp only [h, ite_true]
      ext i
      simp [Counted.forEach, Counted.sub, Counted.mul, Counted.add, hθi]
    · simp [h]
  · simp [HalfspacePresentation.hitAndRunStep, Counted.draw]

/-! ## Cost -/

namespace HitAndRunProg

theorem normalize_cost {m : Nat} (g : Fin (m + 1) → Real) :
    (normalize (m + 1) g).cost = 3 * (m + 1) + 1 := by
  simp only [normalize, Counted.bind_eq, Counted.andThen_cost, Counted.dot_cost, Counted.sqrt,
    Counted.div, Counted.forEach, Counted.mul, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, smul_eq_mul, mul_one]
  ring

theorem facetEndpoints_cost {m : Nat} (a : Fin (m + 1) → Real) (β : Real)
    (x θ : Fin (m + 1) → Real) :
    (facetEndpoints (m + 1) a β x θ).cost = 4 * (m + 1) + 2 := by
  simp only [facetEndpoints, Counted.bind_eq, Counted.andThen_cost, Counted.dot_cost,
    Counted.sub, Counted.div, Counted.lt, Counted.pure_cost]
  ring

theorem chord_cost {m : Nat} : ∀ (r : Nat) (a : Fin r → Fin (m + 1) → Real) (β : Fin r → Real)
    (x θ : Fin (m + 1) → Real), (chord (m + 1) r a β x θ).cost = r * (4 * (m + 1) + 4)
  | 0, a, β, x, θ => by simp [chord]
  | r + 1, a, β, x, θ => by
      simp only [chord, Counted.bind_eq, Counted.andThen_cost, Counted.pure_cost,
        Counted.maxE, Counted.minE, facetEndpoints_cost, chord_cost r]
      ring

end HitAndRunProg

/-- **One step costs at most `4nr + 4r + 6n + 9` operations** (`n ≥ 1`, `r` facets),
including one operation per random number read. -/
theorem HalfspacePresentation.hitAndRunStep_cost_le {n : Nat} (hn : 0 < n)
    (H : HalfspacePresentation n) (x : Point n) (coin : Bool) (g : Point n) (u : Real) :
    (H.hitAndRunStep x coin g u).cost ≤
      4 * n * H.facetCount + 4 * H.facetCount + 6 * n + 9 := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_lt hn
  simp only [zero_add] at *
  cases coin
  · simp only [HalfspacePresentation.hitAndRunStep, Counted.bind_eq, Counted.andThen_cost,
      Counted.draw, Bool.false_eq_true, ite_false, HitAndRunProg.normalize_cost, HitAndRunProg.chord_cost, Counted.toReal, Counted.lt]
    split_ifs
    · simp only [Counted.andThen_cost, Counted.sub, Counted.mul, Counted.add, Counted.forEach,
        Counted.andThen_value, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
        smul_eq_mul]
      nlinarith
    · simp only [Counted.pure_cost]
      nlinarith
  · simp [HalfspacePresentation.hitAndRunStep, Counted.draw]

/-- The charged step cost `hitAndRunStepCost` (the worst case over points and tapes) is at
most `4nr + 4r + 6n + 9`. -/
theorem HalfspacePresentation.hitAndRunStepCost_le {n : Nat} (hn : 0 < n)
    (H : HalfspacePresentation n) :
    H.hitAndRunStepCost ≤ 4 * n * H.facetCount + 4 * H.facetCount + 6 * n + 9 :=
  ciSup_le fun x => ciSup_le fun coin => ciSup_le fun g => ciSup_le fun u =>
    H.hitAndRunStep_cost_le hn x coin g u

/-- The charge for one sampler attempt is at most its closed form. -/
theorem PolytopeData.samplingAttemptCost_le {n : Nat} (hn : 0 < n) (P : PolytopeData n)
    (b : Nat) (eta : Real) (steps : Nat) :
    P.samplingAttemptCost b eta steps ≤
      TTCRuntime.samplingAttemptOperations n P.presentation.facetCount steps := by
  have hstep := (P.hitAndRunPresentation b eta).hitAndRunStepCost_le hn
  rw [PolytopeData.samplingAttemptCost, HalfspacePresentation.memberCost_eq hn,
    TTCRuntime.samplingAttemptOperations, TTCRuntime.hitAndRunStepOperations,
    TTCRuntime.rejectionTestOperations]
  have : steps * (P.hitAndRunPresentation b eta).hitAndRunStepCost ≤
      steps * (4 * n * P.presentation.facetCount + 4 * P.presentation.facetCount + 6 * n + 9) :=
    Nat.mul_le_mul_left _ hstep
  simp only [PolytopeData.scaledPresentation] at *
  omega

/-! ## Probability facts about the tape -/

namespace HitAndRunLaw

open ArlibCommunity.Foundations.Convex (uniformOn)

/-- The uniform law on `[0, 1]`. -/
noncomputable abbrev unitLaw : Measure Real := volume.restrict (Icc (0 : Real) 1)

instance : IsProbabilityMeasure unitLaw := ⟨by simp⟩

/-- `lo + u (hi − lo)` with `u` uniform on `[0, 1]` is uniform on `[lo, hi]`. -/
theorem unitLaw_preimage_affine {lo hi : Real} (h : lo < hi) {T : Set Real}
    (hT : MeasurableSet T) :
    unitLaw ((fun u => lo + u * (hi - lo)) ⁻¹' T) = uniformOn volume (Icc lo hi) T := by
  have hw : 0 < hi - lo := sub_pos.mpr h
  have hpre : (fun u => lo + u * (hi - lo)) ⁻¹' T ∩ Icc 0 1 =
      (fun u => u * (hi - lo)) ⁻¹' ((fun t => lo + t) ⁻¹' (T ∩ Icc lo hi)) := by
    ext u
    simp only [mem_inter_iff, mem_preimage, mem_Icc]
    constructor
    · rintro ⟨hu, h0, h1⟩
      exact ⟨hu, by nlinarith, by nlinarith⟩
    · rintro ⟨hu, h0, h1⟩
      refine ⟨hu, ?_, ?_⟩
      · by_contra hneg
        push Not at hneg
        nlinarith
      · by_contra hneg
        push Not at hneg
        nlinarith
  change volume.restrict (Icc (0 : Real) 1) _ = _
  rw [Measure.restrict_apply (hT.preimage (by fun_prop)), hpre, Real.volume_preimage_mul_right hw.ne', measure_preimage_add,
    ArlibCommunity.Foundations.Convex.uniformOn_def, Measure.smul_apply, smul_eq_mul,
    Measure.restrict_apply hT, Real.volume_Icc, abs_inv, abs_of_pos hw,
    ENNReal.ofReal_inv_of_pos hw]

/-- Averaging over the fair coin. -/
theorem lintegral_fairCoinLaw (f : Bool → ℝ≥0∞) :
    ∫⁻ c, f c ∂fairCoinLaw = 2⁻¹ * f true + 2⁻¹ * f false := by
  have hp : (fairProbability : Real) = 1 / 2 := by
    unfold fairProbability
    rw [Set.projIcc_of_mem _ ⟨by norm_num, by norm_num⟩]
  simp only [fairCoinLaw, bernoulliMeasure, lintegral_add_measure, lintegral_smul_measure,
    lintegral_dirac]
  have h1 : unitInterval.toNNReal fairProbability = 2⁻¹ := by
    ext; simp [unitInterval.toNNReal, hp]; rfl
  have h2 : unitInterval.toNNReal (unitInterval.symm fairProbability) = 2⁻¹ := by
    ext; simp [unitInterval.toNNReal, unitInterval.coe_symm_eq, hp]; norm_num; rfl
  rw [h1, h2, ENNReal.smul_def, ENNReal.smul_def, smul_eq_mul, smul_eq_mul,
    ENNReal.coe_inv two_ne_zero, ENNReal.coe_ofNat]

/-! ## One step, direction by direction -/

open ArlibCommunity.Foundations.MarkovChainTheory
  ArlibCommunity.Foundations.MarkovChainTheory.PolytopeHitAndRunExecution

variable {n : Nat} (H : HalfspacePresentation n) (x : EuclideanSpace Real (Fin n))

/-- The directions along which the chord through `x` is nondegenerate. -/
def goodDirections : Set (Direction n) := {θ | H.lo x θ < H.hi x θ}

theorem measurable_lo {α : Type*} [MeasurableSpace α] {f : α → EuclideanSpace Real (Fin n)}
    (hf : Measurable f) : Measurable (fun a => H.lo x (f a)) :=
  Measurable.comp (g := fun p : PolytopeChord.State n × PolytopeChord.State n => lower (arlibNormals H.normal) H.offset p.1 p.2)
    (f := fun a => (x, f a)) (measurable_lower _ _) (measurable_const.prodMk hf)

theorem measurable_hi {α : Type*} [MeasurableSpace α] {f : α → EuclideanSpace Real (Fin n)}
    (hf : Measurable f) : Measurable (fun a => H.hi x (f a)) :=
  Measurable.comp (g := fun p : PolytopeChord.State n × PolytopeChord.State n => upper (arlibNormals H.normal) H.offset p.1 p.2)
    (f := fun a => (x, f a)) (measurable_upper _ _) (measurable_const.prodMk hf)

theorem measurableSet_goodDirections : MeasurableSet (goodDirections H x) :=
  measurableSet_lt (measurable_lo H x measurable_subtype_coe)
    (measurable_hi H x measurable_subtype_coe)

open Classical in
/-- Along direction `θ`: arlib's uniform point on the chord if it is nondegenerate, otherwise
stay at `x`. -/
noncomputable def directionKernel (H : HalfspacePresentation n) (x : EuclideanSpace Real (Fin n)) :
    ProbabilityTheory.Kernel (Direction n) (EuclideanSpace Real (Fin n)) :=
  ProbabilityTheory.Kernel.piecewise (measurableSet_goodDirections H x)
    (directionEndpointKernel (arlibNormals H.normal) H.offset x)
    (ProbabilityTheory.Kernel.const _ (Measure.dirac x))

open Classical in
theorem directionEndpointKernel_bad {θ : Direction n} (hθ : θ ∉ goodDirections H x) :
    directionEndpointKernel (arlibNormals H.normal) H.offset x θ = 0 := by
  rw [directionEndpointKernel_apply]
  have hle : H.hi x θ ≤ H.lo x θ := not_lt.mp hθ
  have hnull : volume (Icc (H.lo x θ) (H.hi x θ)) = 0 := by
    rw [Real.volume_Icc, ENNReal.ofReal_eq_zero]; linarith
  rw [ArlibCommunity.Foundations.Convex.uniformOn_def, Measure.restrict_eq_zero.mpr hnull,
    smul_zero, Measure.map_zero]

theorem directionEndpointKernel_good_univ {θ : Direction n} (hθ : θ ∈ goodDirections H x) :
    directionEndpointKernel (arlibNormals H.normal) H.offset x θ univ = 1 := by
  rw [directionEndpointKernel_apply, Measure.map_apply (by fun_prop) MeasurableSet.univ,
    preimage_univ]
  have hlt : H.lo x θ < H.hi x θ := hθ
  have h0 : volume (Icc (H.lo x θ) (H.hi x θ)) ≠ 0 := by
    rw [Real.volume_Icc]; simp [hlt]
  have htop : volume (Icc (H.lo x θ) (H.hi x θ)) ≠ ⊤ := by
    rw [Real.volume_Icc]; exact ENNReal.ofReal_ne_top
  have := ArlibCommunity.Foundations.Convex.isProbabilityMeasure_uniformOn volume h0 htop
  exact measure_univ

/-- Averaging `directionEndpointKernel` over directions. -/
theorem proposal_apply [NeZero n] {S : Set (EuclideanSpace Real (Fin n))} (hS : MeasurableSet S) :
    finiteFacetProposal (arlibNormals H.normal) H.offset x S =
      ∫⁻ θ, directionEndpointKernel (arlibNormals H.normal) H.offset x θ S ∂unifSphere n := by
  rw [finiteFacetProposal_apply, Measure.bind_apply hS
    ((ProbabilityTheory.Kernel.aemeasurable
      (directionEndpointKernel (arlibNormals H.normal) H.offset x)).congr
      (Filter.Eventually.of_forall fun θ => directionEndpointKernel_apply _ _ x θ))]
  rfl

open Classical in
/-- **Claim B.** Averaging `directionKernel` over a uniform direction gives arlib's completed
proposal: the proposal plus its stay-put deficit. -/
theorem bind_directionKernel [NeZero n] :
    (unifSphere n).bind (directionKernel H x) =
      finiteFacetProposal (arlibNormals H.normal) H.offset x +
        (1 - finiteFacetProposal (arlibNormals H.normal) H.offset x univ) • Measure.dirac x := by
  have hG := measurableSet_goodDirections H x
  ext S hS
  rw [Measure.bind_apply hS (ProbabilityTheory.Kernel.aemeasurable _), Measure.add_apply,
    Measure.smul_apply, smul_eq_mul, proposal_apply H x hS, proposal_apply H x MeasurableSet.univ]
  have hsplit : ∀ θ, directionKernel H x θ S =
      directionEndpointKernel (arlibNormals H.normal) H.offset x θ S +
        (goodDirections H x)ᶜ.indicator (fun _ => Measure.dirac x S) θ := by
    intro θ
    rw [directionKernel, ProbabilityTheory.Kernel.piecewise_apply']
    by_cases hθ : θ ∈ goodDirections H x
    · simp [hθ]
    · simp [hθ, directionEndpointKernel_bad H x hθ]
  have huniv : ∀ θ, directionEndpointKernel (arlibNormals H.normal) H.offset x θ univ =
      (goodDirections H x).indicator 1 θ := by
    intro θ
    by_cases hθ : θ ∈ goodDirections H x
    · simp [hθ, directionEndpointKernel_good_univ H x hθ]
    · simp [hθ, directionEndpointKernel_bad H x hθ]
  simp_rw [hsplit, huniv]
  rw [lintegral_add_left ((directionEndpointKernel _ _ x).measurable_coe hS),
    lintegral_indicator_const hG.compl, lintegral_indicator_one hG, prob_compl_eq_one_sub hG,
    mul_comm]

/-- The non-lazy move is measurable in the tape. -/
theorem measurable_move :
    Measurable (fun p : EuclideanSpace Real (Fin n) × Real => H.move x p.1 p.2) := by
  have hθ : Measurable (fun p : EuclideanSpace Real (Fin n) × Real => ‖p.1‖⁻¹ • p.1) := by
    fun_prop
  have hlo := measurable_lo H x hθ
  have hhi := measurable_hi H x hθ
  simp only [HalfspacePresentation.move]
  exact Measurable.ite (measurableSet_lt hlo hhi)
    (measurable_const.add ((hlo.add (measurable_snd.mul (hhi.sub hlo))).smul hθ))
    measurable_const

open Classical in
/-- For a fixed Gaussian vector `g ≠ 0`, the move's law over `u` is `directionKernel` at
the direction of `g`. -/
theorem unitLaw_move [NeZero n] {g : EuclideanSpace Real (Fin n)} (hg : g ≠ 0)
    {S : Set (EuclideanSpace Real (Fin n))} (hS : MeasurableSet S) :
    unitLaw {u | H.move x g u ∈ S} = directionKernel H x (GaussianDirection.direction n g) S := by
  have hθ : ((GaussianDirection.direction n g : Direction n) : EuclideanSpace Real (Fin n)) =
      ‖g‖⁻¹ • g := by
    simp [GaussianDirection.direction, GaussianDirection.directionVal, hg]
  rw [directionKernel, ProbabilityTheory.Kernel.piecewise_apply']
  by_cases hgood : GaussianDirection.direction n g ∈ goodDirections H x
  · have hlt : H.lo x (‖g‖⁻¹ • g) < H.hi x (‖g‖⁻¹ • g) := by
      have := hgood; simp only [goodDirections, mem_ofPred_eq, hθ] at this; exact this
    rw [if_pos hgood, directionEndpointKernel_apply, Measure.map_apply (by fun_prop) hS, hθ,
      ← unitLaw_preimage_affine hlt (hS.preimage (by fun_prop))]
    congr 1
    ext u
    simp [HalfspacePresentation.move, hlt]
  · have hlt : ¬ H.lo x (‖g‖⁻¹ • g) < H.hi x (‖g‖⁻¹ • g) := by
      have := hgood; simp only [goodDirections, mem_ofPred_eq, hθ] at this; exact this
    rw [if_neg hgood, ProbabilityTheory.Kernel.const_apply]
    by_cases hxS : x ∈ S <;> simp [HalfspacePresentation.move, hlt, hxS]

/-- **Claim A.** Over a standard Gaussian vector and an independent uniform `u`, the move has
the law of `directionKernel` averaged over a uniform direction. -/
theorem gaussianUnit_map_move [NeZero n] :
    ((stdGaussian (EuclideanSpace Real (Fin n))).prod unitLaw).map
        (fun p => H.move x p.1 p.2) =
      (unifSphere n).bind (directionKernel H x) := by
  ext S hS
  rw [Measure.map_apply (measurable_move H x) hS, Measure.prod_apply (measurable_move H x hS),
    Measure.bind_apply hS (ProbabilityTheory.Kernel.aemeasurable _),
    ← GaussianDirection.stdGaussian_map_direction,
    lintegral_map ((directionKernel H x).measurable_coe hS) GaussianDirection.measurable_direction]
  have hae : ∀ᵐ g ∂stdGaussian (EuclideanSpace Real (Fin n)), g ≠ 0 := by
    rw [ae_iff]
    simp only [ne_eq, not_not, ofPred_eq_eq_singleton]
    rw [GaussianDirection.stdGaussian_apply n (measurableSet_singleton 0)]
    exact setLIntegral_measure_zero _ _ (measure_singleton 0)
  refine lintegral_congr_ae ?_
  filter_upwards [hae] with g hg
  exact unitLaw_move H x hg hS

open Classical in
/-- **One step of the program has arlib's lazy Hit-and-Run law**, at every point of the body. -/
theorem hitAndRunStepLaw_eq [NeZero n]
    (hx : x ∈ ArlibCommunity.Foundations.Convex.Polytope.body (arlibNormals H.normal) H.offset) :
    H.hitAndRunStepLaw x =
      lazy (ArlibCommunity.Algorithms.HitAndRun.finiteFacetStep
        (arlibNormals H.normal) H.offset) x := by
  have hF : (fun ω : Bool × EuclideanSpace Real (Fin n) × Real =>
      WithLp.toLp 2 (H.hitAndRunStep (WithLp.ofLp x) ω.1 (WithLp.ofLp ω.2.1) ω.2.2).value) =
      fun ω => if ω.1 then x else H.move x ω.2.1 ω.2.2 :=
    funext fun ω => H.hitAndRunStep_value x ω.1 ω.2.1 ω.2.2
  have hFm : Measurable (fun ω : Bool × EuclideanSpace Real (Fin n) × Real =>
      if ω.1 then x else H.move x ω.2.1 ω.2.2) :=
    Measurable.ite (measurable_fst (measurableSet_singleton true)) measurable_const
      ((measurable_move H x).comp measurable_snd)
  ext S hS
  rw [HalfspacePresentation.hitAndRunStepLaw, hF, Measure.map_apply hFm hS, hitAndRunTape,
    Measure.prod_apply (hFm hS), lintegral_fairCoinLaw]
  have htrue : ((stdGaussian (EuclideanSpace Real (Fin n))).prod unitLaw)
      (Prod.mk true ⁻¹' ((fun ω : Bool × EuclideanSpace Real (Fin n) × Real =>
        if ω.1 then x else H.move x ω.2.1 ω.2.2) ⁻¹' S)) = Measure.dirac x S := by
    by_cases hxS : x ∈ S
    · rw [show Prod.mk true ⁻¹' _ = univ from eq_univ_of_forall fun p => by simp [hxS]]
      simp [hxS]
    · rw [show Prod.mk true ⁻¹' _ = ∅ from eq_empty_of_forall_notMem fun p => by simp [hxS]]
      simp [hxS]
  have hfalse : ((stdGaussian (EuclideanSpace Real (Fin n))).prod unitLaw)
      (Prod.mk false ⁻¹' ((fun ω : Bool × EuclideanSpace Real (Fin n) × Real =>
        if ω.1 then x else H.move x ω.2.1 ω.2.2) ⁻¹' S)) =
      (((stdGaussian (EuclideanSpace Real (Fin n))).prod unitLaw).map
        (fun p => H.move x p.1 p.2)) S := by
    rw [Measure.map_apply (measurable_move H x) hS]
    rfl
  rw [htrue, hfalse, gaussianUnit_map_move, bind_directionKernel, lazy_apply,
    ArlibCommunity.Algorithms.HitAndRun.finiteFacetStep, finiteFacetHitAndRun,
    ProbabilityTheory.Kernel.piecewise_apply, if_pos hx, finiteFacetHitAndRunAux_apply]
  simp only [Measure.add_apply, Measure.smul_apply, smul_eq_mul]
  ring

/-! ## `T` steps -/

/-- Shorthand for arlib's body of the presentation. -/
abbrev body (H : HalfspacePresentation n) : Set (EuclideanSpace Real (Fin n)) :=
  ArlibCommunity.Foundations.Convex.Polytope.body (arlibNormals H.normal) H.offset

/-- Shorthand for arlib's lazy finite-facet Hit-and-Run kernel. -/
noncomputable abbrev lazyKernel (H : HalfspacePresentation n) :
    ProbabilityTheory.Kernel (EuclideanSpace Real (Fin n)) (EuclideanSpace Real (Fin n)) :=
  lazy (ArlibCommunity.Algorithms.HitAndRun.finiteFacetStep (arlibNormals H.normal) H.offset)

theorem measurableSet_body : MeasurableSet (body H) :=
  ArlibCommunity.Foundations.Convex.Polytope.measurableSet_body _ _

open Classical in
/-- **The walk never leaves a bounded body.** -/
theorem lazyKernel_compl_body [NeZero n] (hK : Bornology.IsBounded (body H)) (hx : x ∈ body H) :
    lazyKernel H x (body H)ᶜ = 0 := by
  have hc := (measurableSet_body H).compl
  have hD : ∀ θ : Direction n,
      directionEndpointKernel (arlibNormals H.normal) H.offset x θ (body H)ᶜ = 0 := by
    intro θ
    have hθ : (θ : EuclideanSpace Real (Fin n)) ≠ 0 := by
      intro h0; have := θ.2; simp [h0] at this
    rw [directionEndpointKernel_apply, Measure.map_apply (by fun_prop) hc,
      ArlibCommunity.Foundations.Convex.uniformOn_def, Measure.smul_apply, smul_eq_mul,
      Measure.restrict_apply (hc.preimage (by fun_prop))]
    have hempty : (fun t : Real => x + t • (θ : EuclideanSpace Real (Fin n))) ⁻¹' (body H)ᶜ ∩
        Icc (H.lo x θ) (H.hi x θ) = ∅ := by
      rw [← chordSet_eq_Icc_of_isBounded hK hx hθ]
      ext t
      simp [ArlibCommunity.Foundations.MarkovChainTheory.chordSet]
    rw [hempty, measure_empty, mul_zero]
  rw [lazy_apply, ArlibCommunity.Algorithms.HitAndRun.finiteFacetStep, finiteFacetHitAndRun,
    ProbabilityTheory.Kernel.piecewise_apply, if_pos hx, finiteFacetHitAndRunAux_apply]
  have hdirac : Measure.dirac x (body H)ᶜ = 0 := by
    rw [Measure.dirac_apply' _ hc, Set.indicator_of_notMem (Set.notMem_compl_iff.mpr hx)]
  simp only [Measure.add_apply, Measure.smul_apply, smul_eq_mul, proposal_apply H x hc, hD,
    lintegral_zero, hdirac, mul_zero, add_zero]

/-- **`T` steps of the program have the law of arlib's `T`-step lazy Hit-and-Run chain**, from
any start law on a bounded body. -/
theorem hitAndRunWalk_eq_iterate [NeZero n] (hK : Bornology.IsBounded (body H))
    (μ : Measure (EuclideanSpace Real (Fin n))) (hμ : μ (body H)ᶜ = 0) :
    ∀ T, H.hitAndRunWalk μ T = iterate (lazyKernel H) μ T ∧
      H.hitAndRunWalk μ T (body H)ᶜ = 0
  | 0 => ⟨rfl, hμ⟩
  | T + 1 => by
      obtain ⟨heq, hnull⟩ := hitAndRunWalk_eq_iterate hK μ hμ T
      have hae : ∀ᵐ y ∂H.hitAndRunWalk μ T, y ∈ body H := ae_iff.mpr hnull
      have hbind : H.hitAndRunWalk μ (T + 1) = (H.hitAndRunWalk μ T).bind (lazyKernel H) := by
        change Measure.join ((H.hitAndRunWalk μ T).map H.hitAndRunStepLaw) =
          Measure.join ((H.hitAndRunWalk μ T).map (lazyKernel H))
        rw [Measure.map_congr (hae.mono fun y hy => hitAndRunStepLaw_eq H y hy)]
      refine ⟨?_, ?_⟩
      · rw [hbind, heq]; rfl
      · rw [hbind, Measure.bind_apply (measurableSet_body H).compl
          (ProbabilityTheory.Kernel.aemeasurable _)]
        refine (lintegral_congr_ae (hae.mono fun y hy => ?_)).trans lintegral_zero
        exact lazyKernel_compl_body H y hK hy

end HitAndRunLaw

end ttc

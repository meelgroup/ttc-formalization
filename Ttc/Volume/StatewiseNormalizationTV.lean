import Ttc.Volume.CVPathwisePhaseKernel

/-! Quantitative comparison of statewise and after-mixing normalization. -/

namespace Ttc.StatewiseNormalizationTV

open MeasureTheory ProbabilityTheory Set
open Arlib Ttc.CVPathwisePhaseKernel
open scoped ENNReal Classical

variable {A B : Type*} [MeasurableSpace A] [MeasurableSpace B]

/-- Mutual multiplicative domination of probability laws gives an additive TV bound.
The loss `c - 1` is useful only when the domination factor is close to one. -/
theorem tvLe_of_mutual_le_mul
    (mu nu : Measure B) [IsProbabilityMeasure mu] [IsProbabilityMeasure nu]
    {c : ENNReal} (hc : 1 ≤ c) (hctop : c ≠ ⊤)
    (hmunu : ∀ S, MeasurableSet S → mu S ≤ c * nu S)
    (hnumu : ∀ S, MeasurableSet S → nu S ≤ c * mu S) :
    TVLe mu nu (c - 1) := by
  intro S hS
  have hmuTop : mu S ≠ ⊤ := measure_ne_top mu S
  have hnuTop : nu S ≠ ⊤ := measure_ne_top nu S
  have hsubTop : c - 1 ≠ ⊤ := ENNReal.sub_ne_top hctop
  have haddNu : nu S + (c - 1) ≠ ⊤ := ENNReal.add_ne_top.2 ⟨hnuTop, hsubTop⟩
  have haddMu : mu S + (c - 1) ≠ ⊤ := ENNReal.add_ne_top.2 ⟨hmuTop, hsubTop⟩
  constructor
  · rw [← ENNReal.toReal_le_toReal hmuTop haddNu,
      ENNReal.toReal_add hnuTop hsubTop,
      ENNReal.toReal_sub_of_le hc hctop]
    simp only [ENNReal.toReal_one]
    have hmul := ENNReal.toReal_mono
      (ENNReal.mul_ne_top hctop hnuTop) (hmunu S hS)
    rw [ENNReal.toReal_mul] at hmul
    have hnuOne : (nu S).toReal ≤ 1 := by
      simpa using ENNReal.toReal_mono ENNReal.one_ne_top
        (prob_le_one (μ := nu) (s := S))
    have hcReal : 1 ≤ c.toReal := by
      simpa using ENNReal.toReal_mono hctop hc
    nlinarith [ENNReal.toReal_nonneg (a := nu S), ENNReal.toReal_nonneg (a := c)]
  · rw [← ENNReal.toReal_le_toReal hnuTop haddMu,
      ENNReal.toReal_add hmuTop hsubTop,
      ENNReal.toReal_sub_of_le hc hctop]
    simp only [ENNReal.toReal_one]
    have hmul := ENNReal.toReal_mono
      (ENNReal.mul_ne_top hctop hmuTop) (hnumu S hS)
    rw [ENNReal.toReal_mul] at hmul
    have hmuOne : (mu S).toReal ≤ 1 := by
      simpa using ENNReal.toReal_mono ENNReal.one_ne_top
        (prob_le_one (μ := mu) (s := S))
    have hcReal : 1 ≤ c.toReal := by
      simpa using ENNReal.toReal_mono hctop hc
    nlinarith [ENNReal.toReal_nonneg (a := mu S), ENNReal.toReal_nonneg (a := c)]

theorem div_le_mul_div_of_le
    {R Q a b : ENNReal} (hRtop : R ≠ ⊤) (hQ0 : Q ≠ 0) (hQtop : Q ≠ ⊤)
    (ha0 : a ≠ 0) (hatop : a ≠ ⊤) (hbtop : b ≠ ⊤) (hQb : Q ≤ b) :
    R / a ≤ (b / a) * (R / Q) := by
  have hLtop : R / a ≠ ⊤ := ENNReal.div_ne_top hRtop ha0
  have hbdivtop : b / a ≠ ⊤ := ENNReal.div_ne_top hbtop ha0
  have hRdivtop : R / Q ≠ ⊤ := ENNReal.div_ne_top hRtop hQ0
  have hRtop' : (b / a) * (R / Q) ≠ ⊤ :=
    ENNReal.mul_ne_top hbdivtop hRdivtop
  rw [← ENNReal.toReal_le_toReal hLtop hRtop', ENNReal.toReal_div,
    ENNReal.toReal_mul, ENNReal.toReal_div, ENNReal.toReal_div]
  have ha : 0 < a.toReal := ENNReal.toReal_pos ha0 hatop
  have hQ : 0 < Q.toReal := ENNReal.toReal_pos hQ0 hQtop
  have hQb' : Q.toReal ≤ b.toReal := ENNReal.toReal_mono hbtop hQb
  have hR : 0 ≤ R.toReal := ENNReal.toReal_nonneg
  field_simp
  nlinarith

theorem div_le_mul_of_le_mul
    {R Q a b U : ENNReal} (hRtop : R ≠ ⊤) (hQ0 : Q ≠ 0) (hQtop : Q ≠ ⊤)
    (ha0 : a ≠ 0) (hatop : a ≠ ⊤) (hbtop : b ≠ ⊤) (hUtop : U ≠ ⊤)
    (haQ : a ≤ Q) (hR : R ≤ b * U) :
    R / Q ≤ (b / a) * U := by
  have hLtop : R / Q ≠ ⊤ := ENNReal.div_ne_top hRtop hQ0
  have hbdivtop : b / a ≠ ⊤ := ENNReal.div_ne_top hbtop ha0
  have hRtop' : (b / a) * U ≠ ⊤ := ENNReal.mul_ne_top hbdivtop hUtop
  rw [← ENNReal.toReal_le_toReal hLtop hRtop', ENNReal.toReal_div,
    ENNReal.toReal_mul, ENNReal.toReal_div]
  have ha : 0 < a.toReal := ENNReal.toReal_pos ha0 hatop
  have hQ : 0 < Q.toReal := ENNReal.toReal_pos hQ0 hQtop
  have haQ' : a.toReal ≤ Q.toReal := ENNReal.toReal_mono hQtop haQ
  have hR' := ENNReal.toReal_mono (ENNReal.mul_ne_top hbtop hUtop) hR
  rw [ENNReal.toReal_mul] at hR'
  have hU : 0 ≤ U.toReal := ENNReal.toReal_nonneg
  have hb : 0 ≤ b.toReal := ENNReal.toReal_nonneg
  field_simp
  calc
    R.toReal * a.toReal ≤ (b.toReal * U.toReal) * a.toReal :=
      mul_le_mul_of_nonneg_right hR' ha.le
    _ ≤ (b.toReal * U.toReal) * Q.toReal :=
      mul_le_mul_of_nonneg_left haQ' (mul_nonneg hb hU)
    _ = Q.toReal * b.toReal * U.toReal := by ring

/-- If every fiber mass lies in `[a,b]`, mixing normalized fibers and normalizing the
mixed finite kernel are mutually dominated by `b/a`. -/
theorem bind_normalizeOr_mutual_le_mul
    (rho : Measure A) [IsProbabilityMeasure rho]
    (kappa fallback : Kernel A B) [IsFiniteKernel kappa] [IsMarkovKernel fallback]
    {a b : ENNReal} (ha : 0 < a) (hatop : a ≠ ⊤) (hbtop : b ≠ ⊤)
    (hmass : ∀ x, a ≤ kappa x Set.univ ∧ kappa x Set.univ ≤ b) :
    let mu := rho.bind (normalizeOr kappa fallback)
    let nu := Arlib.condOn (rho.bind kappa) Set.univ
    (∀ S, MeasurableSet S → mu S ≤ (b / a) * nu S) ∧
      (∀ S, MeasurableSet S → nu S ≤ (b / a) * mu S) := by
  dsimp only
  let raw := rho.bind kappa
  have hQformula : raw Set.univ = ∫⁻ x, kappa x Set.univ ∂rho := by
    rw [Measure.bind_apply MeasurableSet.univ kappa.aemeasurable]
  have haQ : a ≤ raw Set.univ := by
    rw [hQformula]
    calc
      a = ∫⁻ _x : A, a ∂rho := by simp
      _ ≤ ∫⁻ x, kappa x Set.univ ∂rho :=
        lintegral_mono fun x => (hmass x).1
  have hQb : raw Set.univ ≤ b := by
    rw [hQformula]
    calc
      ∫⁻ x, kappa x Set.univ ∂rho ≤ ∫⁻ _x : A, b ∂rho :=
        lintegral_mono fun x => (hmass x).2
      _ = b := by simp
  have hQ0 : raw Set.univ ≠ 0 := ne_of_gt (lt_of_lt_of_le ha haQ)
  have hQtop : raw Set.univ ≠ ⊤ := measure_ne_top raw Set.univ
  have hfiber0 : ∀ x, kappa x Set.univ ≠ 0 := fun x =>
    ne_of_gt (lt_of_lt_of_le ha (hmass x).1)
  constructor
  · intro S hS
    rw [bind_normalizeOr_apply rho kappa fallback hfiber0 hS,
      Arlib.condOn_apply raw MeasurableSet.univ hS, Set.inter_univ]
    have hRtop : raw S ≠ ⊤ := measure_ne_top raw S
    calc
      ∫⁻ x, kappa x S / kappa x Set.univ ∂rho ≤
          ∫⁻ x, a⁻¹ * kappa x S ∂rho := by
        apply lintegral_mono
        intro x
        simpa [ENNReal.div_eq_inv_mul] using
          ENNReal.div_le_div_left (hmass x).1 (kappa x S)
      _ = a⁻¹ * raw S := by
        rw [lintegral_const_mul' _ _ (ENNReal.inv_ne_top.2 ha.ne'),
          Measure.bind_apply hS kappa.aemeasurable]
      _ = raw S / a := by rw [ENNReal.div_eq_inv_mul]
      _ ≤ (b / a) * (raw S / raw Set.univ) :=
        div_le_mul_div_of_le hRtop hQ0 hQtop ha.ne' hatop hbtop hQb
  · intro S hS
    rw [bind_normalizeOr_apply rho kappa fallback hfiber0 hS,
      Arlib.condOn_apply raw MeasurableSet.univ hS, Set.inter_univ]
    have hRtop : raw S ≠ ⊤ := measure_ne_top raw S
    have hUtop : (∫⁻ x, kappa x S / kappa x Set.univ ∂rho) ≠ ⊤ := by
      rw [← bind_normalizeOr_apply rho kappa fallback hfiber0 hS]
      exact measure_ne_top (rho.bind (normalizeOr kappa fallback)) S
    have hRU : raw S ≤
        b * (∫⁻ x, kappa x S / kappa x Set.univ ∂rho) := by
      rw [Measure.bind_apply hS kappa.aemeasurable]
      calc
        ∫⁻ x, kappa x S ∂rho ≤
            ∫⁻ x, b * (kappa x S / kappa x Set.univ) ∂rho := by
          apply lintegral_mono
          intro x
          have hp0 := hfiber0 x
          have hptop : kappa x Set.univ ≠ ⊤ := measure_ne_top (kappa x) Set.univ
          calc
            kappa x S = kappa x S / kappa x Set.univ * kappa x Set.univ :=
              (ENNReal.div_mul_cancel hp0 hptop).symm
            _ ≤ kappa x S / kappa x Set.univ * b :=
              mul_le_mul_left' (hmass x).2 _
            _ = b * (kappa x S / kappa x Set.univ) := by ac_rfl
        _ = b * (∫⁻ x, kappa x S / kappa x Set.univ ∂rho) :=
          lintegral_const_mul' _ _ hbtop
    exact div_le_mul_of_le_mul hRtop hQ0 hQtop ha.ne' hatop hbtop hUtop haQ hRU

/-- Quantitative normalization mismatch.  The error vanishes only when the fiber masses
are uniformly close (`b/a → 1`); a mere constant lower bound gives a constant TV loss. -/
theorem tvLe_bind_normalizeOr_condOn_bind
    (rho : Measure A) [IsProbabilityMeasure rho]
    (kappa fallback : Kernel A B) [IsFiniteKernel kappa] [IsMarkovKernel fallback]
    {a b : ENNReal} (ha : 0 < a) (hatop : a ≠ ⊤) (hbtop : b ≠ ⊤)
    (hab : a ≤ b)
    (hmass : ∀ x, a ≤ kappa x Set.univ ∧ kappa x Set.univ ≤ b) :
    TVLe (rho.bind (normalizeOr kappa fallback))
      (Arlib.condOn (rho.bind kappa) Set.univ) (b / a - 1) := by
  let raw := rho.bind kappa
  have hraw0 : raw Set.univ ≠ 0 := by
    rw [Measure.bind_apply MeasurableSet.univ kappa.aemeasurable]
    exact ne_of_gt (lt_of_lt_of_le ha <| by
      calc
        a = ∫⁻ _x : A, a ∂rho := by simp
        _ ≤ ∫⁻ x, kappa x Set.univ ∂rho :=
          lintegral_mono fun x => (hmass x).1)
  letI : IsProbabilityMeasure (Arlib.condOn raw Set.univ) :=
    Arlib.isProbabilityMeasure_condOn _ hraw0 (measure_ne_top raw Set.univ)
  have hmut := bind_normalizeOr_mutual_le_mul rho kappa fallback ha hatop hbtop hmass
  apply tvLe_of_mutual_le_mul
  · rw [ENNReal.div_eq_inv_mul]
    calc
      1 = a⁻¹ * a := (ENNReal.inv_mul_cancel ha.ne' hatop).symm
      _ ≤ a⁻¹ * b := mul_le_mul_left' hab _
  · exact ENNReal.div_ne_top hbtop ha.ne'
  · exact hmut.1
  · exact hmut.2

/-! ## A finite obstruction to an `o(1)` bound from constant acceptance alone -/

theorem normalizationMismatch_fiber_mass_bounds (x : Bool) :
    (2 : ENNReal)⁻¹ ≤ normalizationMismatchKernel x Set.univ ∧
      normalizationMismatchKernel x Set.univ ≤ 1 := by
  rw [normalizationMismatchKernel_apply, Measure.smul_apply, smul_eq_mul,
    Measure.dirac_apply' _ MeasurableSet.univ]
  cases x <;> norm_num

theorem bind_normalizationMismatch_eq_piHalf :
    Arlib.MarkovChains.piHalf.bind
        (normalizeOr normalizationMismatchKernel Kernel.id) =
      Arlib.MarkovChains.piHalf := by
  rw [normalizeOr_normalizationMismatchKernel_eq_id, Measure.id_comp]

theorem raw_normalizationMismatch_eq :
    Arlib.MarkovChains.piHalf.bind normalizationMismatchKernel =
      (1 / 2 : ENNReal) • Measure.dirac true +
        (1 / 4 : ENNReal) • Measure.dirac false := by
  rw [Arlib.MarkovChains.piHalf, Measure.comp_smul, Measure.comp_add]
  simp only [Measure.dirac_bind normalizationMismatchKernel.measurable,
    normalizationMismatchKernel_apply]
  simp only [if_true, Bool.false_eq_true, if_false, one_smul, smul_add]
  rw [smul_smul]
  congr 1
  symm
  have h4 : (4 : ENNReal) = 2 * 2 := by norm_num
  rw [h4]
  exact congrArg (fun z : ENNReal => z • Measure.dirac false) (by
    simpa only [one_div] using
      (ENNReal.mul_inv (a := (2 : ENNReal)) (b := (2 : ENNReal))
        (by simp) (by simp)))

theorem condOn_raw_normalizationMismatch_true :
    Arlib.condOn
      (Arlib.MarkovChains.piHalf.bind normalizationMismatchKernel) Set.univ
      ({true} : Set Bool) = 2 / 3 := by
  rw [raw_normalizationMismatch_eq,
    Arlib.condOn_apply _ MeasurableSet.univ (MeasurableSet.singleton true)]
  simp only [Set.inter_univ, Measure.add_apply, Measure.smul_apply, smul_eq_mul,
    Measure.dirac_apply' _ (MeasurableSet.singleton true),
    Measure.dirac_apply' _ MeasurableSet.univ,
    Set.indicator_of_mem (Set.mem_singleton true),
    Set.indicator_of_notMem (by simp : false ∉ ({true} : Set Bool)),
    Pi.one_apply, Set.indicator_of_mem (Set.mem_univ true),
    Set.indicator_of_mem (Set.mem_univ false), mul_one, mul_zero, add_zero]
  rw [← ENNReal.toReal_eq_toReal_iff'
      (ENNReal.div_ne_top (by finiteness) (by norm_num)) (by finiteness),
    ENNReal.toReal_div, ENNReal.toReal_add (by finiteness) (by finiteness),
    ENNReal.toReal_div, ENNReal.toReal_div]
  norm_num

/-- Even with every acceptance mass in `[1/2,1]`, statewise normalization remains at
TV distance at least `1/6` from normalize-after-mixing.  Thus a fixed source lower bound
cannot yield an error tending to zero with the mixing tolerance. -/
theorem one_six_le_of_tvLe_normalizationMismatch {eps : ENNReal}
    (h : TVLe
      (Arlib.MarkovChains.piHalf.bind
        (normalizeOr normalizationMismatchKernel Kernel.id))
      (Arlib.condOn
        (Arlib.MarkovChains.piHalf.bind normalizationMismatchKernel) Set.univ)
      eps) :
    ENNReal.ofReal (1 / 6 : Real) ≤ eps := by
  have hevent := h.right (MeasurableSet.singleton true)
  rw [bind_normalizationMismatch_eq_piHalf,
    Arlib.MarkovChains.piHalf_singleton,
    condOn_raw_normalizationMismatch_true] at hevent
  have hepsTop : eps = ⊤ ∨ eps ≠ ⊤ := eq_or_ne eps ⊤
  rcases hepsTop with rfl | hepsTop
  · simp
  · rw [← ENNReal.toReal_le_toReal ENNReal.ofReal_ne_top hepsTop,
      ENNReal.toReal_ofReal (by norm_num : (0 : Real) ≤ 1 / 6)]
    have hreal := ENNReal.toReal_mono
      (ENNReal.add_ne_top.2 ⟨by norm_num, hepsTop⟩) hevent
    rw [ENNReal.toReal_div, ENNReal.toReal_add (by finiteness) hepsTop,
      ENNReal.toReal_div] at hreal
    norm_num at hreal
    linarith

#print axioms tvLe_bind_normalizeOr_condOn_bind
#print axioms one_six_le_of_tvLe_normalizationMismatch

end Ttc.StatewiseNormalizationTV

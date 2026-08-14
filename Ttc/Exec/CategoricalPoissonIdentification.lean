import Ttc.Exec.CostedMarkedPoissonIdentified
import Mathlib.Data.Fintype.Perm

namespace Ttc.CostedMarkedPoissonIdentified

open MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators Classical NNReal

variable {L N : Nat}

/-- The multiplicity vector of a finite categorical word. -/
def finiteHistogram (c : Fin N → Fin L) (a : Fin L) : Nat :=
  Fintype.card {j : Fin N // c j = a}

private def sigmaFstFiberEquiv (r : Fin L → Nat) (a : Fin L) :
    {z : (Σ b : Fin L, Fin (r b)) // z.1 = a} ≃ Fin (r a) where
  toFun z := by
    rcases z with ⟨⟨b, k⟩, hb⟩
    change b = a at hb
    subst b
    exact k
  invFun k := ⟨⟨a, k⟩, rfl⟩
  left_inv z := by
    rcases z with ⟨⟨b, k⟩, hb⟩
    change b = a at hb
    subst b
    rfl
  right_inv k := rfl

private def occurrenceFiberEquiv (r : Fin L → Nat)
    (e : Fin N ≃ (Σ a : Fin L, Fin (r a))) (a : Fin L) :
    {j : Fin N // (e j).1 = a} ≃ Fin (r a) :=
  (e.subtypeEquiv fun _ => Iff.rfl).trans (sigmaFstFiberEquiv r a)

private def labeledHistogramEquiv (r : Fin L → Nat) :
    (Fin N ≃ (Σ a : Fin L, Fin (r a))) ≃
      (Σ c : {c : Fin N → Fin L // finiteHistogram c = r},
        ∀ a, {j : Fin N // c.1 j = a} ≃ Fin (r a)) where
  toFun e := by
    let c : Fin N → Fin L := fun j => (e j).1
    have hc : finiteHistogram c = r := by
      funext a
      simpa [finiteHistogram] using Fintype.card_congr (occurrenceFiberEquiv r e a)
    exact ⟨⟨c, hc⟩, fun a => occurrenceFiberEquiv r e a⟩
  invFun p :=
    (Equiv.sigmaFiberEquiv p.1.1).symm.trans (Equiv.sigmaCongrRight p.2)
  left_inv e := by
    apply Equiv.ext
    intro j
    simp [occurrenceFiberEquiv, sigmaFstFiberEquiv]
    change ⟨(e j).1, (e j).2⟩ = e j
    exact Sigma.eta _
  right_inv p := by
    rcases p with ⟨⟨c, hc⟩, lab⟩
    change (let c' : Fin N → Fin L := fun j => c j
      let hc' : finiteHistogram c' = r := by
        funext a
        simpa [finiteHistogram] using Fintype.card_congr (occurrenceFiberEquiv r
          ((Equiv.sigmaFiberEquiv c).symm.trans (Equiv.sigmaCongrRight lab)) a)
      (⟨⟨c', hc'⟩, fun a => occurrenceFiberEquiv r
        ((Equiv.sigmaFiberEquiv c).symm.trans (Equiv.sigmaCongrRight lab)) a⟩ :
          (Σ c : {c : Fin N → Fin L // finiteHistogram c = r},
            ∀ a, {j : Fin N // c.1 j = a} ≃ Fin (r a)))) = ⟨⟨c, hc⟩, lab⟩
    dsimp only
    congr 1
    funext a
    apply Equiv.ext
    intro j
    rcases j with ⟨j, hj⟩
    change c j = a at hj
    subst a
    change (lab (c j)) ⟨j, _⟩ = (lab (c j)) ⟨j, _⟩
    congr

/-- Cardinality of the histogram fiber: the multinomial coefficient. -/
theorem card_finiteHistogram_fiber (r : Fin L → Nat)
    (hsum : ∑ a, r a = N) :
    Fintype.card {c : Fin N → Fin L // finiteHistogram c = r} =
      Nat.multinomial Finset.univ r := by
  let O := Σ a : Fin L, Fin (r a)
  have hcardO : Fintype.card O = N := by
    simp [O, hsum]
  let eON : O ≃ Fin N := Fintype.equivOfCardEq (by simpa using hcardO)
  have hleft : Fintype.card (Fin N ≃ O) = Nat.factorial N := by
    rw [Fintype.card_equiv eON.symm, Fintype.card_fin]
  have hright : Fintype.card
      (Σ c : {c : Fin N → Fin L // finiteHistogram c = r},
        ∀ a, {j : Fin N // c.1 j = a} ≃ Fin (r a)) =
      Fintype.card {c : Fin N → Fin L // finiteHistogram c = r} *
        ∏ a, Nat.factorial (r a) := by
    rw [Fintype.card_sigma]
    simp only [Fintype.card_pi]
    have hlabel : ∀ c : {c : Fin N → Fin L // finiteHistogram c = r},
        (∏ a, Fintype.card ({j : Fin N // c.1 j = a} ≃ Fin (r a))) =
          ∏ a, Nat.factorial (r a) := by
      intro c
      apply Finset.prod_congr rfl
      intro a ha
      have hca : Fintype.card {j : Fin N // c.1 j = a} = r a := by
        simpa [finiteHistogram] using congrFun c.2 a
      let ea : {j : Fin N // c.1 j = a} ≃ Fin (r a) :=
        Fintype.equivOfCardEq (by simpa using hca)
      simpa [hca] using Fintype.card_equiv ea
    simp_rw [hlabel]
    rw [Finset.sum_const, nsmul_eq_mul]
    simp
  have hcount := Fintype.card_congr (labeledHistogramEquiv (N := N) r)
  rw [hleft, hright] at hcount
  have hspec := Nat.multinomial_spec Finset.univ r
  rw [hsum] at hspec
  have hprod : 0 < ∏ a, Nat.factorial (r a) :=
    Finset.prod_pos fun _ _ => Nat.factorial_pos _
  apply Nat.eq_of_mul_eq_mul_right hprod
  calc
    Fintype.card {c : Fin N → Fin L // finiteHistogram c = r} *
        ∏ a, Nat.factorial (r a) = Nat.factorial N := hcount.symm
    _ = (∏ a, Nat.factorial (r a)) * Nat.multinomial Finset.univ r := hspec.symm
    _ = Nat.multinomial Finset.univ r * ∏ a, Nat.factorial (r a) := mul_comm _ _

def takeFin (N : Nat) (omega : Nat → Fin L) : Fin N → Fin L :=
  fun j => omega j

theorem measurable_takeFin (N : Nat) : Measurable (takeFin (L := L) N) := by
  exact measurable_pi_iff.2 fun j => measurable_pi_apply (j : Nat)

/-- The first `N` coordinates of an infinite iid stream have the finite product law. -/
theorem map_takeFin_infinitePi (N : Nat) (mu : Measure (Fin L))
    [IsProbabilityMeasure mu] :
    Measure.map (takeFin N) (Measure.infinitePi fun _ : Nat => mu) =
      Measure.pi (fun _ : Fin N => mu) := by
  refine Measure.ext_of_singleton fun c => ?_
  rw [Measure.map_apply (measurable_takeFin N) (MeasurableSet.singleton c)]
  let t : Nat → Set (Fin L) := fun i =>
    if h : i < N then {c ⟨i, h⟩} else Set.univ
  have hpre : takeFin N ⁻¹' {c} = Set.pi (Finset.range N) t := by
    ext omega
    simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_pi, Finset.mem_coe,
      Finset.mem_range]
    constructor
    · intro homega i hi
      have hv := congrFun homega ⟨i, hi⟩
      simpa [takeFin, t, hi] using hv
    · intro homega
      funext j
      simpa [takeFin, t] using homega (j : Nat) j.isLt
  rw [hpre, Measure.infinitePi_pi]
  · have hbox : ({c} : Set (Fin N → Fin L)) =
        Set.univ.pi (fun j => ({c j} : Set (Fin L))) := by
      ext d
      simp only [Set.mem_singleton_iff, Set.mem_pi, Set.mem_univ, true_implies]
      exact ⟨fun h => by subst d; simp, fun h => funext h⟩
    rw [hbox, Measure.pi_pi]
    calc
      (∏ i ∈ Finset.range N, mu (t i)) =
          ∏ i ∈ Finset.range N,
            if h : i < N then mu {c ⟨i, h⟩} else 1 := by
              apply Finset.prod_congr rfl
              intro i hi
              rw [Finset.mem_range] at hi
              simp [t, hi]
      _ = ∏ j, mu {c j} :=
        by simpa using (Fin.prod_univ_eq_prod_range
          (fun i => if h : i < N then mu {c ⟨i, h⟩} else 1) N).symm
  · intro i hi
    simp [t, hi]

/-- Products of categorical weights depend only on the histogram. -/
theorem prod_eq_prod_pow_finiteHistogram {M : Type*} [CommMonoid M]
    (q : Fin L → M) (c : Fin N → Fin L) :
    (∏ j, q (c j)) = ∏ a, q a ^ finiteHistogram c a := by
  rw [← Fintype.prod_fiberwise' c q]
  apply Finset.prod_congr rfl
  intro a ha
  simp [finiteHistogram]

/-- The exact finite-sample multinomial mass of one histogram. -/
theorem map_finiteHistogram_pi_singleton {q : Fin L → Real}
    (hq0 : ∀ a, 0 ≤ q a) (hq : ∑ a, q a = 1)
    (N : Nat) (r : Fin L → Nat) :
    Measure.map finiteHistogram (Measure.pi fun _ : Fin N => categoricalLaw q) {r} =
      if h : ∑ a, r a = N then
        ENNReal.ofReal ((Nat.multinomial Finset.univ r : Real) * ∏ a, q a ^ r a)
      else 0 := by
  letI : IsProbabilityMeasure (categoricalLaw q) :=
    isProbabilityMeasure_categoricalLaw hq0 hq
  rw [Measure.map_apply (measurable_pi_iff.2 fun _ => Measurable.of_discrete)
    (MeasurableSet.singleton r)]
  by_cases hsum : ∑ a, r a = N
  · rw [dif_pos hsum]
    let fiber : Finset (Fin N → Fin L) :=
      Finset.univ.filter fun c => finiteHistogram c = r
    have hset : finiteHistogram ⁻¹' {r} = (fiber : Set (Fin N → Fin L)) := by
      ext c
      simp [fiber]
    rw [hset, ← sum_measure_singleton]
    have hmass : ∀ c ∈ fiber,
        (Measure.pi fun _ : Fin N => categoricalLaw q) {c} =
          ENNReal.ofReal (∏ a, q a ^ r a) := by
      intro c hc
      have hcr : finiteHistogram c = r := by simpa [fiber] using hc
      have hbox : ({c} : Set (Fin N → Fin L)) =
          Set.univ.pi (fun j => ({c j} : Set (Fin L))) := by
        ext d
        simp only [Set.mem_singleton_iff, Set.mem_pi, Set.mem_univ, true_implies]
        exact ⟨fun h => by subst d; simp, fun h => funext h⟩
      rw [hbox, Measure.pi_pi]
      simp only [categoricalLaw_singleton]
      rw [← ENNReal.ofReal_prod_of_nonneg fun j _ => hq0 (c j)]
      congr 1
      rw [prod_eq_prod_pow_finiteHistogram q c, hcr]
    rw [Finset.sum_congr rfl hmass, Finset.sum_const, nsmul_eq_mul]
    have hfcard : fiber.card =
        Fintype.card {c : Fin N → Fin L // finiteHistogram c = r} := by
      simp [fiber, Fintype.card_subtype]
    rw [hfcard, card_finiteHistogram_fiber r hsum]
    rw [← ENNReal.ofReal_natCast]
    rw [← ENNReal.ofReal_mul (by positivity)]
  · rw [dif_neg hsum]
    have hempty : (finiteHistogram (N := N)) ⁻¹' {r} =
        (∅ : Set (Fin N → Fin L)) := by
      apply Set.eq_empty_iff_forall_notMem.2
      intro c hc
      have hcr : finiteHistogram c = r := by simpa using hc
      apply hsum
      rw [← hcr]
      calc
        (∑ a, finiteHistogram c a) =
            Fintype.card (Σ a : Fin L, {j : Fin N // c j = a}) := by
              simp [finiteHistogram, Fintype.card_sigma]
        _ = Fintype.card (Fin N) :=
          Fintype.card_congr (Equiv.sigmaFiberEquiv c)
        _ = N := Fintype.card_fin N
    simp [hempty]

theorem finiteHistogram_takeFin_eq (N : Nat) (omega : Nat → Fin L) (a : Fin L) :
    finiteHistogram (takeFin N omega) a =
      ∑ j ∈ Finset.range N, if omega j = a then 1 else 0 := by
  rw [finiteHistogram, Fintype.card_subtype]
  change (Finset.univ.filter fun x : Fin N => omega x = a).card = _
  calc
    (Finset.univ.filter fun x : Fin N => omega x = a).card =
        ∑ j : Fin N, if omega j = a then 1 else 0 :=
      (Finset.sum_boole (R := Nat) (fun x : Fin N => omega x = a) Finset.univ).symm
    _ = ∑ j ∈ Finset.range N, if omega j = a then 1 else 0 :=
      Fin.sum_univ_eq_sum_range (fun j => if omega j = a then 1 else 0) N

def pureRandomHistogram (p : Nat × (Nat → Fin L)) : Fin L → Nat :=
  finiteHistogram (takeFin p.1 p.2)

theorem measurable_pureRandomHistogram :
    Measurable (pureRandomHistogram (L := L)) := by
  apply measurable_from_prod_countable_right
  intro N
  apply measurable_pi_lambda
  intro a
  change Measurable fun omega : Nat → Fin L => finiteHistogram (takeFin N omega) a
  rw [show (fun omega : Nat → Fin L => finiteHistogram (takeFin N omega) a) =
      fun omega => ∑ j ∈ Finset.range N, if omega j = a then 1 else 0 by
        funext omega
        exact finiteHistogram_takeFin_eq N omega a]
  apply Finset.measurable_sum
  intro j hj
  exact Measurable.ite
    ((MeasurableSet.singleton a).preimage (measurable_pi_apply j))
    measurable_const measurable_const

theorem pureRandomHistogram_eq (p : Nat × (Nat → Fin L)) :
    pureRandomHistogram p = fun a =>
      ∑ j ∈ Finset.range p.1, if p.2 j = a then 1 else 0 := by
  funext a
  exact finiteHistogram_takeFin_eq p.1 p.2 a

theorem map_fixedHistogram_infinitePi {q : Fin L → Real}
    (hq0 : ∀ a, 0 ≤ q a) (hq : ∑ a, q a = 1) (N : Nat) :
    Measure.map (fun omega : Nat → Fin L => finiteHistogram (takeFin N omega))
        (Measure.infinitePi fun _ : Nat => categoricalLaw q) =
      Measure.map finiteHistogram (Measure.pi fun _ : Fin N => categoricalLaw q) := by
  letI : IsProbabilityMeasure (categoricalLaw q) :=
    isProbabilityMeasure_categoricalLaw hq0 hq
  have hcomp : (fun omega : Nat → Fin L => finiteHistogram (takeFin N omega)) =
      finiteHistogram ∘ takeFin N := rfl
  rw [hcomp, ← Measure.map_map (measurable_pi_iff.2 fun _ => Measurable.of_discrete)
    (measurable_takeFin N)]
  rw [map_takeFin_infinitePi]

/-- Poisson many iid categorical marks have exactly the repository's `countLaw`. -/
theorem categoricalPoissonIdentified {lam : Real} (hlam : 0 ≤ lam)
    {q : Fin L → Real} (hq0 : ∀ a, 0 ≤ q a) (hq : ∑ a, q a = 1) :
    CategoricalPoissonIdentified lam q := by
  letI : IsProbabilityMeasure (categoricalLaw q) :=
    isProbabilityMeasure_categoricalLaw hq0 hq
  constructor
  refine Measure.ext_of_singleton fun r => ?_
  rw [iidMarkedCountLaw]
  rw [show (fun p : Nat × (Nat → Fin L) =>
        fun a => ∑ j ∈ Finset.range p.1, if p.2 j = a then 1 else 0) =
        pureRandomHistogram by
          funext p
          exact (pureRandomHistogram_eq p).symm]
  rw [Measure.map_apply measurable_pureRandomHistogram (MeasurableSet.singleton r)]
  ·
    rw [Measure.prod_apply ((MeasurableSet.singleton r).preimage
      measurable_pureRandomHistogram)]
    have hsection : ∀ N : Nat,
        (Measure.infinitePi fun _ : Nat => categoricalLaw q)
            (Prod.mk N ⁻¹' (pureRandomHistogram ⁻¹' {r})) =
          if h : ∑ a, r a = N then
            ENNReal.ofReal ((Nat.multinomial Finset.univ r : Real) * ∏ a, q a ^ r a)
          else 0 := by
      intro N
      rw [show Prod.mk N ⁻¹' (pureRandomHistogram ⁻¹' {r}) =
          (fun omega : Nat → Fin L => finiteHistogram (takeFin N omega)) ⁻¹' {r} by rfl]
      have hmfixed : Measurable
          (fun omega : Nat → Fin L => finiteHistogram (takeFin N omega)) :=
        by
          change Measurable
            (pureRandomHistogram ∘ fun omega : Nat → Fin L => (N, omega))
          exact measurable_pureRandomHistogram.comp
            (measurable_const.prodMk measurable_id)
      rw [← Measure.map_apply
        hmfixed
        (MeasurableSet.singleton r)]
      rw [map_fixedHistogram_infinitePi hq0 hq N]
      exact map_finiteHistogram_pi_singleton hq0 hq N r
    simp_rw [hsection]
    rw [lintegral_countable']
    let s : Nat := ∑ a, r a
    rw [tsum_eq_single s]
    · simp only [s, dif_pos]
      rw [poissonMeasure_singleton, countLaw_singleton, poissonPMF_def,
        Real.coe_toNNReal lam hlam]
      rw [← ENNReal.ofReal_mul (mul_nonneg (Nat.cast_nonneg _)
        (Finset.prod_nonneg fun a _ => pow_nonneg (hq0 a) _))]
    · intro N hNs
      have hne : ¬∑ a, r a = N := by
        simpa [s, eq_comm] using hNs
      simp [hne]

#print axioms card_finiteHistogram_fiber
#print axioms map_finiteHistogram_pi_singleton
#print axioms categoricalPoissonIdentified

end Ttc.CostedMarkedPoissonIdentified

import Kr25Ssmxt.Analysis.L2LatticeDeflate
import ArlibCommunity.Algorithms.KV97.Analysis.Escape
import ArlibCommunity.Algorithms.KV97.Analysis.ContTent
import ArlibCommunity.Algorithms.KV97.Analysis.KernelIntegral

/-! # Lemma `lem:nonconv`: lattice points versus volume for a union of polytopes

Let `Q = ⋃ᵢ Pᵢ` be a union of `m` bounded polytopes in `ℝⁿ`, each containing an
`ℓ₂` ball of radius `γ ≥ (64 m n / η) √(log (4 r / η))`, where `r` bounds every
facet count (the paper takes the total). Then

  `(1 - η) |Q ∩ ℤⁿ| ≤ vol Q ≤ (1 + η) |Q ∩ ℤⁿ|`.

The proof follows the paper. With `κ = √(2 log (8/η)) + √(2 log r)`, let `Q'`
and `Q''` be the unions of the `κ`-inflations and `κ`-deflations, and let
`K(z, p) = ∏ₖ tent (pₖ - zₖ)` be the randomized-rounding kernel.

* For every lattice point `z ∈ Q`, `∫_{Q'} K(z, ·) ≥ 1 - η/8` (claim (a)).
* For every `p ∈ Q''`, `∑_{z ∈ Q ∩ ℤⁿ} K(z, p) ≥ 1 - η/8` (claim (b)).
* `∫ K(z, ·) ≤ 1` and `∑_z K(z, p) ≤ 1` (claim (c)).

Exchanging the finite sum with the integral gives
`(1 - η/8) N ≤ vol Q'` and `(1 - η/8) vol Q'' ≤ N`. The homothety bounds give
`vol Q' ≤ (1 + η/13) vol Q` and `vol Q ≤ vol Q'' + (η/26) vol Q`, since
`κ/γ ≤ η/(26 m n)`. (The paper states `η/(32 m n)`; the ratio
`log (8r/η) / log (4r/η)` can reach `3/2`, which gives `26`. The escape bound
here is `η/8` rather than the paper's `η/4`, so the conclusion is unchanged.) -/

namespace Kr25Ssmxt

open MeasureTheory Set ArlibCommunity.Algorithms.KV97
open scoped InnerProductSpace

variable {n : ℕ}

/-- An integer vector as a point of Euclidean space. -/
noncomputable def intPoint (z : Fin n → ℤ) : EuclideanSpace ℝ (Fin n) :=
  WithLp.toLp 2 (fun k => (z k : ℝ))

@[simp] theorem intPoint_apply (z : Fin n → ℤ) (k : Fin n) :
    intPoint z k = (z k : ℝ) := rfl

/-- The kernel at an integer point is the rounding law's point mass. -/
theorem prodTent_intPoint_eq (z : Fin n → ℤ) (p : EuclideanSpace ℝ (Fin n)) :
    prodTent (intPoint z) p = (roundLaw (WithLp.ofLp p)).real {z} := by
  rw [measureReal_def, roundLaw_singleton,
    ENNReal.toReal_ofReal (Finset.prod_nonneg fun i _ => tent_nonneg _)]
  rfl

/-- Summing the kernel over a finite set of integer points gives the rounding
law's mass of that set; in particular at most `1`. -/
theorem sum_prodTent_eq (T : Finset (Fin n → ℤ)) (p : EuclideanSpace ℝ (Fin n)) :
    ∑ z ∈ T, prodTent (intPoint z) p = (roundLaw (WithLp.ofLp p)).real T := by
  simp only [prodTent_intPoint_eq]
  exact sum_measureReal_singleton T

theorem sum_prodTent_le_one (T : Finset (Fin n → ℤ)) (p : EuclideanSpace ℝ (Fin n)) :
    ∑ z ∈ T, prodTent (intPoint z) p ≤ 1 := by
  rw [sum_prodTent_eq]
  exact measureReal_le_one

/-- The arithmetic of `κ / γ`. -/
theorem kappa_div_le {m : ℕ} {η r γ : ℝ} (hm : 0 < m) (hn : 0 < n)
    (hη0 : 0 < η) (hη1 : η ≤ 1) (hr : 1 ≤ r)
    (hγ : (64 * m * n / η) * Real.sqrt (Real.log (4 * r / η)) ≤ γ) :
    ArlibCommunity.Algorithms.KV97.kappaOf (Real.sqrt (2 * Real.log (8 / η))) r / γ ≤
      η / (26 * m * n) := by
  set L := Real.log (4 * r / η) with hL
  have h4 : (4 : ℝ) ≤ 4 * r / η := by
    rw [le_div_iff₀ hη0]; nlinarith
  have hlog4 : Real.log 4 ≤ L := Real.log_le_log (by norm_num) h4
  have hlog2 : Real.log 2 * 2 = Real.log 4 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; push_cast; ring
  have hlog2pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hLpos : 0 < L := by linarith
  have h8 : Real.log (8 / η) + Real.log r = Real.log 2 + L := by
    rw [hL, ← Real.log_mul (by positivity) (by linarith),
      ← Real.log_mul (by norm_num) (by positivity)]
    congr 1; field_simp; ring
  have hlog8 : 0 ≤ Real.log (8 / η) := Real.log_nonneg (by
    rw [le_div_iff₀ hη0]; linarith)
  have hlogr : 0 ≤ Real.log r := Real.log_nonneg hr
  set a := Real.sqrt (2 * Real.log (8 / η))
  set c := Real.sqrt (2 * Real.log r)
  have ha2 : a ^ 2 = 2 * Real.log (8 / η) := Real.sq_sqrt (by linarith)
  have hc2 : c ^ 2 = 2 * Real.log r := Real.sq_sqrt (by linarith)
  have ha0 : 0 ≤ a := Real.sqrt_nonneg _
  have hc0 : 0 ≤ c := Real.sqrt_nonneg _
  have hκ : ArlibCommunity.Algorithms.KV97.kappaOf a r = a + c := rfl
  have hκsq : (a + c) ^ 2 ≤ 6 * L := by
    nlinarith [sq_nonneg (a - c)]
  set s := Real.sqrt L
  have hs2 : s ^ 2 = L := Real.sq_sqrt hLpos.le
  have hspos : 0 < s := Real.sqrt_pos.mpr hLpos
  have hκle : a + c ≤ (64 / 26) * s := by
    have h6 : (a + c) ^ 2 ≤ ((64 / 26) * s) ^ 2 := by nlinarith
    exact (pow_le_pow_iff_left₀ (by positivity) (by positivity) two_ne_zero).mp h6
  have hmn : (0 : ℝ) < m * n := by positivity
  have hγpos : 0 < γ := lt_of_lt_of_le (by positivity) hγ
  rw [hκ, div_le_div_iff₀ hγpos (by positivity)]
  have hγ' : 64 * m * n * s ≤ γ * η := by
    rw [div_mul_eq_mul_div, div_le_iff₀ hη0] at hγ; linarith
  nlinarith

/-- `exp (-c²/2) = η/8` at `c = √(2 log (8/η))`. -/
theorem exp_escape_eq {η : ℝ} (hη0 : 0 < η) (hη1 : η ≤ 1) :
    Real.exp (-(Real.sqrt (2 * Real.log (8 / η))) ^ 2 / 2) = η / 8 := by
  have hlog8 : 0 ≤ Real.log (8 / η) := Real.log_nonneg (by
    rw [le_div_iff₀ hη0]; linarith)
  rw [Real.sq_sqrt (by linarith)]
  have : -(2 * Real.log (8 / η)) / 2 = -Real.log (8 / η) := by ring
  rw [this, Real.exp_neg, Real.exp_log (by positivity)]
  field_simp

section Union

variable {m : ℕ} {f : Fin m → ℕ}
  (A : (i : Fin m) → Fin (f i) → EuclideanSpace ℝ (Fin n))
  (b : (i : Fin m) → Fin (f i) → ℝ)

/-- **Claim (a).** A lattice point of `Q` keeps kernel mass at least `1 - η/8`
inside the union of the inflations. -/
theorem claim_inflate_mass {η r : ℝ} (hη0 : 0 < η) (hη1 : η ≤ 1) (hr1 : 1 ≤ r)
    (hf : ∀ i, (f i : ℝ) ≤ r) {z : Fin n → ℤ}
    (hz : intPoint z ∈ ⋃ i, ArlibCommunity.Foundations.Convex.Polytope.body (A i) (b i)) :
    1 - η / 8 ≤ ∫ p in ⋃ i, ArlibCommunity.Foundations.Convex.Polytope.inflate (A i) (b i)
        (ArlibCommunity.Algorithms.KV97.kappaOf (Real.sqrt (2 * Real.log (8 / η))) r),
      prodTent (intPoint z) p := by
  obtain ⟨i, hi⟩ := mem_iUnion.mp hz
  set κ := ArlibCommunity.Algorithms.KV97.kappaOf (Real.sqrt (2 * Real.log (8 / η))) r
  have hesc := setIntegral_prodTent_compl_inflate_le_exp (A i) (b i) hi
    (c := Real.sqrt (2 * Real.log (8 / η))) (Real.sqrt_nonneg _) hr1 (by simpa using hf i)
  rw [exp_escape_eq hη0 hη1] at hesc
  have hmeas : MeasurableSet (ArlibCommunity.Foundations.Convex.Polytope.inflate (A i) (b i) κ) :=
    ArlibCommunity.Foundations.Convex.Polytope.measurableSet_inflate _ _ _
  have hlow : 1 - η / 8 ≤ ∫ p in ArlibCommunity.Foundations.Convex.Polytope.inflate (A i) (b i) κ,
      prodTent (intPoint z) p := by
    rw [setIntegral_prodTent_compl _ hmeas]; linarith
  exact hlow.trans (setIntegral_prodTent_mono _ (subset_iUnion
    (fun j => ArlibCommunity.Foundations.Convex.Polytope.inflate (A j) (b j) κ) i) hmeas
    (MeasurableSet.iUnion fun j => ArlibCommunity.Foundations.Convex.Polytope.measurableSet_inflate _ _ _))

/-- **Claim (b).** A point of the union of the deflations rounds into `Q` with
probability at least `1 - η/8`. -/
theorem claim_deflate_mass {η r : ℝ} (hη0 : 0 < η) (hη1 : η ≤ 1) (hr1 : 1 ≤ r)
    (hf : ∀ i, (f i : ℝ) ≤ r) {p : EuclideanSpace ℝ (Fin n)}
    (hp : p ∈ ⋃ i, ArlibCommunity.Foundations.Convex.Polytope.inflate (A i) (b i)
      (-ArlibCommunity.Algorithms.KV97.kappaOf (Real.sqrt (2 * Real.log (8 / η))) r))
    (T : Finset (Fin n → ℤ))
    (hT : ∀ z, intPoint z ∈ ⋃ i, ArlibCommunity.Foundations.Convex.Polytope.body (A i) (b i) → z ∈ T) :
    1 - η / 8 ≤ ∑ z ∈ T, prodTent (intPoint z) p := by
  obtain ⟨i, hi⟩ := mem_iUnion.mp hp
  set κ := ArlibCommunity.Algorithms.KV97.kappaOf (Real.sqrt (2 * Real.log (8 / η))) r
  set μ := roundLaw (WithLp.ofLp p)
  let A' : Fin (f i) → EuclideanSpace ℝ (Fin n) := fun j => -A i j
  let b' : Fin (f i) → ℝ := fun j => b i j - ⟪A i j, p⟫_ℝ - κ * ‖A i j‖
  have h0 : (0 : EuclideanSpace ℝ (Fin n)) ∈ ArlibCommunity.Foundations.Convex.Polytope.body A' b' := by
    intro j
    have := hi j
    simp only [A', b', inner_zero_right]
    linarith
  have hesc := ArlibCommunity.Algorithms.KV97.roundLaw_escape_prob_le_exp A' b' (WithLp.ofLp p) h0
    (c := Real.sqrt (2 * Real.log (8 / η))) (Real.sqrt_nonneg _) hr1 (by simpa using hf i)
  rw [exp_escape_eq hη0 hη1] at hesc
  have hdisp : ∀ z, ArlibCommunity.Algorithms.KV97.latDispVec (WithLp.ofLp p) z = p - intPoint z := by
    intro z; ext k; simp [ArlibCommunity.Algorithms.KV97.latDispVec, intPoint]
  have hsub : {z : Fin n → ℤ | intPoint z ∉ ArlibCommunity.Foundations.Convex.Polytope.body (A i) (b i)} ⊆
      {z | 0 + ArlibCommunity.Algorithms.KV97.latDispVec (WithLp.ofLp p) z ∉
        ArlibCommunity.Foundations.Convex.Polytope.inflate A' b' κ} := by
    intro z hz hin
    apply hz
    intro j
    have := hin j
    simp only [zero_add, hdisp, A', b', inner_neg_left, inner_sub_right, norm_neg] at this
    linarith
  have hcompl : μ.real {z : Fin n → ℤ | intPoint z ∉ ArlibCommunity.Foundations.Convex.Polytope.body (A i) (b i)}
      ≤ η / 8 := (measureReal_mono hsub).trans hesc
  have hmeasS : MeasurableSet {z : Fin n → ℤ | intPoint z ∈ ArlibCommunity.Foundations.Convex.Polytope.body (A i) (b i)} :=
    (Set.to_countable _).measurableSet
  have hsum := measureReal_add_measureReal_compl (μ := μ) hmeasS
  rw [probReal_univ] at hsum
  have hTsub : {z : Fin n → ℤ | intPoint z ∈ ArlibCommunity.Foundations.Convex.Polytope.body (A i) (b i)} ⊆ (T : Set _) :=
    fun z hz => hT z (mem_iUnion.mpr ⟨i, hz⟩)
  have hmono := measureReal_mono (μ := μ) hTsub
  rw [sum_prodTent_eq]
  change 1 - η / 8 ≤ μ.real T
  have : {z : Fin n → ℤ | intPoint z ∈ ArlibCommunity.Foundations.Convex.Polytope.body (A i) (b i)}ᶜ =
      {z : Fin n → ℤ | intPoint z ∉ ArlibCommunity.Foundations.Convex.Polytope.body (A i) (b i)} := rfl
  rw [this] at hsum
  linarith

end Union

/-- The integer points of a bounded set form a finite set. -/
theorem finite_intPoints {Q : Set (EuclideanSpace ℝ (Fin n))}
    (hQ : Bornology.IsBounded Q) : {z : Fin n → ℤ | intPoint z ∈ Q}.Finite := by
  obtain ⟨R, hR⟩ := hQ.subset_closedBall 0
  apply (Set.Finite.pi (t := fun _ : Fin n => Set.Icc (-⌈R⌉) ⌈R⌉)
    fun _ => Set.finite_Icc _ _).subset
  intro z hz
  have hnorm : ‖intPoint z‖ ≤ R := by
    have := hR hz
    rwa [Metric.mem_closedBall, dist_zero_right] at this
  have hk : ∀ k, |(z k : ℝ)| ≤ R := fun k => by
    have := (PiLp.norm_apply_le (intPoint z) k).trans hnorm
    simpa [intPoint, Real.norm_eq_abs] using this
  intro k _
  have h1 := abs_le.mp (hk k)
  have h2 := Int.le_ceil R
  constructor
  · have : ((-⌈R⌉ : ℤ) : ℝ) ≤ (z k : ℝ) := by push_cast; linarith
    exact_mod_cast this
  · have : (z k : ℝ) ≤ ((⌈R⌉ : ℤ) : ℝ) := by linarith
    exact_mod_cast this

section Main

variable {m : ℕ} {f : Fin m → ℕ}
  (A : (i : Fin m) → Fin (f i) → EuclideanSpace ℝ (Fin n))
  (b : (i : Fin m) → Fin (f i) → ℝ)

set_option maxHeartbeats 1000000 in
/-- **Lemma `lem:nonconv`** (union of polytopes with `ℓ₂` inballs). -/
theorem l2_union_lattice_comparison {η r γ : ℝ} (hm : 0 < m) (hn : 0 < n)
    (hη0 : 0 < η) (hη1 : η ≤ 1) (hr1 : 1 ≤ r) (hf : ∀ i, (f i : ℝ) ≤ r)
    (hγ : (64 * m * n / η) * Real.sqrt (Real.log (4 * r / η)) ≤ γ)
    (cen : Fin m → EuclideanSpace ℝ (Fin n))
    (hball : ∀ i, Metric.ball (cen i) γ ⊆ ArlibCommunity.Foundations.Convex.Polytope.body (A i) (b i))
    (hbdd : ∀ i, Bornology.IsBounded (ArlibCommunity.Foundations.Convex.Polytope.body (A i) (b i))) :
    (1 - η) * ({z : Fin n → ℤ | intPoint z ∈ ⋃ i, ArlibCommunity.Foundations.Convex.Polytope.body (A i) (b i)}.ncard : ℝ)
        ≤ volume.real (⋃ i, ArlibCommunity.Foundations.Convex.Polytope.body (A i) (b i)) ∧
      volume.real (⋃ i, ArlibCommunity.Foundations.Convex.Polytope.body (A i) (b i)) ≤
        (1 + η) * ({z : Fin n → ℤ | intPoint z ∈ ⋃ i, ArlibCommunity.Foundations.Convex.Polytope.body (A i) (b i)}.ncard : ℝ) := by
  classical
  set κ := ArlibCommunity.Algorithms.KV97.kappaOf (Real.sqrt (2 * Real.log (8 / η))) r with hκdef
  set P := fun i => ArlibCommunity.Foundations.Convex.Polytope.body (A i) (b i) with hPdef
  set P' := fun i => ArlibCommunity.Foundations.Convex.Polytope.inflate (A i) (b i) κ with hP'def
  set P'' := fun i => ArlibCommunity.Foundations.Convex.Polytope.inflate (A i) (b i) (-κ) with hP''def
  set Q := ⋃ i, P i with hQdef
  set Q' := ⋃ i, P' i with hQ'def
  set Q'' := ⋃ i, P'' i with hQ''def
  -- geometry constants
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hL : 0 < Real.log (4 * r / η) := Real.log_pos (by
    rw [lt_div_iff₀ hη0]; nlinarith)
  have hγpos : 0 < γ := lt_of_lt_of_le (by positivity) hγ
  have hκ0 : 0 ≤ κ := ArlibCommunity.Algorithms.KV97.kappaOf_nonneg (Real.sqrt_nonneg _)
  set t := κ / γ with htdef
  have ht0 : 0 ≤ t := div_nonneg hκ0 hγpos.le
  have ht : t ≤ η / (26 * m * n) := kappa_div_le hm hn hη0 hη1 hr1 hγ
  have hmnt : (m : ℝ) * n * t ≤ η / 26 := by
    have := mul_le_mul_of_nonneg_left ht (by positivity : (0 : ℝ) ≤ m * n)
    calc (m : ℝ) * n * t ≤ m * n * (η / (26 * m * n)) := this
      _ = η / 26 := by field_simp
  have hnt : (n : ℝ) * t ≤ 1 / 26 := by
    have h1 : (n : ℝ) * t ≤ m * n * t := by
      have : (1 : ℝ) ≤ m := by exact_mod_cast hm
      nlinarith [mul_nonneg hnR.le ht0]
    linarith
  have hκγ : κ ≤ γ := by
    have h1 : t ≤ 1 := by
      have : t ≤ n * t := by
        have : (1 : ℝ) ≤ n := by exact_mod_cast hn
        nlinarith
      linarith
    rwa [htdef, div_le_one hγpos] at h1
  -- measurability and finiteness
  have hPm : ∀ i, MeasurableSet (P i) := fun i => ArlibCommunity.Foundations.Convex.Polytope.measurableSet_body _ _
  have hP'm : ∀ i, MeasurableSet (P' i) := fun i => ArlibCommunity.Foundations.Convex.Polytope.measurableSet_inflate _ _ _
  have hP''m : ∀ i, MeasurableSet (P'' i) := fun i => ArlibCommunity.Foundations.Convex.Polytope.measurableSet_inflate _ _ _
  have hQ'm : MeasurableSet Q' := MeasurableSet.iUnion hP'm
  have hQ''m : MeasurableSet Q'' := MeasurableSet.iUnion hP''m
  have hPfin : ∀ i, volume (P i) ≠ ⊤ := fun i => (hbdd i).measure_lt_top.ne
  have hP'le : ∀ i, volume (P' i) ≤ ENNReal.ofReal ((1 + t) ^ n) * volume (P i) :=
    fun i => ArlibCommunity.Foundations.Convex.Polytope.volume_inflate_le hγpos hκ0 (hball i)
  have hP'fin : ∀ i, volume (P' i) ≠ ⊤ := fun i =>
    ne_top_of_le_ne_top (ENNReal.mul_ne_top ENNReal.ofReal_ne_top (hPfin i)) (hP'le i)
  have hQb : Bornology.IsBounded Q := Bornology.isBounded_iUnion.mpr hbdd
  have hQfin : volume Q ≠ ⊤ := hQb.measure_lt_top.ne
  have hQ'fin : volume Q' ≠ ⊤ := by
    refine ne_top_of_le_ne_top ?_ (measure_iUnion_fintype_le volume P')
    exact ENNReal.sum_ne_top.mpr fun i _ => hP'fin i
  have hPP' : ∀ i, P i ⊆ P' i := fun i =>
    ArlibCommunity.Foundations.Convex.Polytope.body_subset_inflate (A i) (b i) hκ0
  have hP''P : ∀ i, P'' i ⊆ P i := fun i => by
    have := ArlibCommunity.Foundations.Convex.Polytope.inflate_mono (A i) (b i) (neg_nonpos.mpr hκ0)
    rwa [ArlibCommunity.Foundations.Convex.Polytope.inflate_zero] at this
  have hQ''Q : Q'' ⊆ Q := iUnion_mono hP''P
  -- the finite set of lattice points
  have hS := finite_intPoints hQb
  set T := hS.toFinset with hTdef
  have hmemT : ∀ z, z ∈ T ↔ intPoint z ∈ Q := fun z => by simp [T]
  have hN : ({z : Fin n → ℤ | intPoint z ∈ Q}.ncard : ℝ) = T.card := by
    rw [Set.ncard_eq_toFinset_card _ hS]
  rw [hN]
  -- double counting over `Q'`
  have hcountA : (1 - η / 8) * T.card ≤ volume.real Q' := by
    have h1 : ∀ z ∈ T, 1 - η / 8 ≤ ∫ p in Q', prodTent (intPoint z) p :=
      fun z hz => claim_inflate_mass A b hη0 hη1 hr1 hf ((hmemT z).mp hz)
    have h2 : (1 - η / 8) * T.card ≤ ∑ z ∈ T, ∫ p in Q', prodTent (intPoint z) p := by
      calc (1 - η / 8) * T.card = ∑ _z ∈ T, (1 - η / 8) := by
            rw [Finset.sum_const, nsmul_eq_mul, mul_comm]
        _ ≤ _ := Finset.sum_le_sum h1
    have h3 : ∑ z ∈ T, ∫ p in Q', prodTent (intPoint z) p =
        ∫ p in Q', ∑ z ∈ T, prodTent (intPoint z) p :=
      (integral_finsetSum T fun z _ => integrableOn_prodTent _ _).symm
    have : IsFiniteMeasure (volume.restrict Q') := isFiniteMeasure_restrict.mpr hQ'fin
    have h4 : ∫ p in Q', ∑ z ∈ T, prodTent (intPoint z) p ≤ ∫ _ in Q', (1 : ℝ) :=
      setIntegral_mono_on (integrable_finsetSum T fun z _ => integrableOn_prodTent _ _)
        (integrable_const 1) hQ'm fun p _ => sum_prodTent_le_one T p
    rw [setIntegral_const, smul_eq_mul, mul_one] at h4
    linarith
  -- double counting over `Q''`
  have hcountB : (1 - η / 8) * volume.real Q'' ≤ T.card := by
    have hQ''fin : volume Q'' ≠ ⊤ := ne_top_of_le_ne_top hQfin (measure_mono hQ''Q)
    have : IsFiniteMeasure (volume.restrict Q'') := isFiniteMeasure_restrict.mpr hQ''fin
    have h1 : ∫ _ in Q'', (1 - η / 8 : ℝ) ≤ ∫ p in Q'', ∑ z ∈ T, prodTent (intPoint z) p :=
      setIntegral_mono_on (integrable_const _)
        (integrable_finsetSum T fun z _ => integrableOn_prodTent _ _) hQ''m
        fun p hp => claim_deflate_mass A b hη0 hη1 hr1 hf hp T fun z hz => (hmemT z).mpr hz
    rw [setIntegral_const, smul_eq_mul] at h1
    have h2 : ∫ p in Q'', ∑ z ∈ T, prodTent (intPoint z) p =
        ∑ z ∈ T, ∫ p in Q'', prodTent (intPoint z) p :=
      integral_finsetSum T fun z _ => integrableOn_prodTent _ _
    have h3 : ∑ z ∈ T, ∫ p in Q'', prodTent (intPoint z) p ≤ ∑ _z ∈ T, (1 : ℝ) :=
      Finset.sum_le_sum fun z _ => setIntegral_prodTent_le_one _ hQ''m
    simp only [Finset.sum_const, nsmul_eq_mul, mul_one] at h3
    linarith
  -- volume of the inflated union
  have hPQ : ∀ i, volume.real (P i) ≤ volume.real Q := fun i =>
    measureReal_mono (subset_iUnion P i) hQfin
  have hP'real : ∀ i, volume.real (P' i) ≤ (1 + t) ^ n * volume.real (P i) := fun i => by
    have h := ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.ofReal_ne_top (hPfin i)) (hP'le i)
    rwa [ENNReal.toReal_mul, ENNReal.toReal_ofReal (pow_nonneg (by linarith) n)] at h
  have hP''real : ∀ i, (1 - t) ^ n * volume.real (P i) ≤ volume.real (P'' i) := fun i => by
    have h := ENNReal.toReal_mono
      (ne_top_of_le_ne_top (hPfin i) (measure_mono (hP''P i)))
      (volume_deflate_ge hγpos hκ0 hκγ (hball i))
    rwa [ENNReal.toReal_mul, ENNReal.toReal_ofReal
      (pow_nonneg (by rw [sub_nonneg, div_le_one hγpos]; exact hκγ) n)] at h
  have hQ'eq : Q' = Q ∪ ⋃ i, (P' i \ P i) := by
    ext x
    simp only [hQ'def, hQdef, mem_union, mem_iUnion, mem_diff]
    constructor
    · rintro ⟨i, hi⟩
      by_cases h : x ∈ P i
      · exact Or.inl ⟨i, h⟩
      · exact Or.inr ⟨i, hi, h⟩
    · rintro (⟨i, hi⟩ | ⟨i, hi, _⟩)
      · exact ⟨i, hPP' i hi⟩
      · exact ⟨i, hi⟩
  have hQeq : Q = Q'' ∪ ⋃ i, (P i \ P'' i) := by
    ext x
    simp only [hQ''def, hQdef, mem_union, mem_iUnion, mem_diff]
    constructor
    · rintro ⟨i, hi⟩
      by_cases h : x ∈ P'' i
      · exact Or.inl ⟨i, h⟩
      · exact Or.inr ⟨i, hi, h⟩
    · rintro (⟨i, hi⟩ | ⟨i, hi, _⟩)
      · exact ⟨i, hP''P i hi⟩
      · exact ⟨i, hi⟩
  have hpow1 : (1 + t) ^ n - 1 ≤ 2 * n * t := by
    have := one_add_pow_le_one_add_two_mul ht0 n (by linarith)
    linarith
  have hpow2 : 1 - (1 - t) ^ n ≤ n * t := by
    have := one_sub_mul_le_one_sub_pow (t := t) (by
      have : t ≤ n * t := by
        have : (1 : ℝ) ≤ n := by exact_mod_cast hn
        nlinarith
      linarith) n
    linarith
  have hX0 : 0 ≤ volume.real Q := measureReal_nonneg
  have hQ'bound : volume.real Q' ≤ (1 + η / 13) * volume.real Q := by
    have h1 : volume.real Q' ≤ volume.real Q + ∑ i, volume.real (P' i \ P i) := by
      rw [hQ'eq]
      exact (measureReal_union_le _ _).trans
        (add_le_add_right (measureReal_iUnion_fintype_le _) _)
    have h2 : ∀ i, volume.real (P' i \ P i) ≤ (2 * n * t) * volume.real Q := fun i => by
      rw [measureReal_sdiff (hPP' i) (hPm i) (hP'fin i)]
      have := hP'real i
      have hPi0 : 0 ≤ volume.real (P i) := measureReal_nonneg
      have h3 : ((1 + t) ^ n - 1) * volume.real (P i) ≤ (2 * n * t) * volume.real (P i) :=
        mul_le_mul_of_nonneg_right hpow1 hPi0
      have h4 : (2 * n * t) * volume.real (P i) ≤ (2 * n * t) * volume.real Q :=
        mul_le_mul_of_nonneg_left (hPQ i) (by positivity)
      nlinarith
    have h5 : ∑ i, volume.real (P' i \ P i) ≤ m * ((2 * n * t) * volume.real Q) := by
      have := Finset.sum_le_sum fun i (_ : i ∈ Finset.univ) => h2 i
      simpa [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] using this
    have h6 : (m : ℝ) * ((2 * n * t) * volume.real Q) ≤ η / 13 * volume.real Q := by
      have : (m : ℝ) * (2 * n * t) ≤ η / 13 := by nlinarith
      nlinarith
    linarith
  have hQbound : volume.real Q ≤ volume.real Q'' + η / 26 * volume.real Q := by
    have h1 : volume.real Q ≤ volume.real Q'' + ∑ i, volume.real (P i \ P'' i) := by
      conv_lhs => rw [hQeq]
      exact (measureReal_union_le _ _).trans
        (add_le_add_right (measureReal_iUnion_fintype_le _) _)
    have h2 : ∀ i, volume.real (P i \ P'' i) ≤ (n * t) * volume.real Q := fun i => by
      rw [measureReal_sdiff (hP''P i) (hP''m i) (hPfin i)]
      have := hP''real i
      have hPi0 : 0 ≤ volume.real (P i) := measureReal_nonneg
      have h3 : (1 - (1 - t) ^ n) * volume.real (P i) ≤ (n * t) * volume.real (P i) :=
        mul_le_mul_of_nonneg_right hpow2 hPi0
      have h4 : (n * t) * volume.real (P i) ≤ (n * t) * volume.real Q :=
        mul_le_mul_of_nonneg_left (hPQ i) (by positivity)
      nlinarith
    have h5 : ∑ i, volume.real (P i \ P'' i) ≤ m * ((n * t) * volume.real Q) := by
      have := Finset.sum_le_sum fun i (_ : i ∈ Finset.univ) => h2 i
      simpa [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] using this
    have h6 : (m : ℝ) * ((n * t) * volume.real Q) ≤ η / 26 * volume.real Q := by
      have : (m : ℝ) * (n * t) ≤ η / 26 := by nlinarith
      nlinarith
    linarith
  -- the final arithmetic
  set X := volume.real Q
  set N := (T.card : ℝ)
  have hN0 : 0 ≤ N := Nat.cast_nonneg _
  have hY''0 : 0 ≤ volume.real Q'' := measureReal_nonneg
  constructor
  · have hc : (1 - η) * (1 + η / 13) ≤ 1 - η / 8 := by nlinarith
    have h1 : (1 - η) * N * (1 + η / 13) ≤ (1 - η / 8) * N := by
      have := mul_le_mul_of_nonneg_right hc hN0
      linarith
    have h2 : (1 - η / 8) * N ≤ X * (1 + η / 13) := by
      have := hcountA.trans hQ'bound
      linarith
    exact le_of_mul_le_mul_right (h1.trans h2) (by positivity)
  · have h1 : X * (1 - η / 26) ≤ volume.real Q'' := by linarith
    have h2 : X * ((1 - η / 26) * (1 - η / 8)) ≤ N := by
      have := mul_le_mul_of_nonneg_right h1 (by linarith : (0 : ℝ) ≤ 1 - η / 8)
      have h' : X * (1 - η / 26) * (1 - η / 8) = X * ((1 - η / 26) * (1 - η / 8)) := by ring
      linarith
    have h3 : 1 ≤ (1 + η) * ((1 - η / 26) * (1 - η / 8)) := by
      nlinarith [mul_nonneg hη0.le (sub_nonneg.mpr hη1), pow_pos hη0 3, sq_nonneg η]
    calc X ≤ X * ((1 + η) * ((1 - η / 26) * (1 - η / 8))) := le_mul_of_one_le_right hX0 h3
      _ = (1 + η) * (X * ((1 - η / 26) * (1 - η / 8))) := by ring
      _ ≤ (1 + η) * N := mul_le_mul_of_nonneg_left h2 (by linarith)

end Main

end Kr25Ssmxt

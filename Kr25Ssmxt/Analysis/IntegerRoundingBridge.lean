import Kr25Ssmxt.Analysis.ArlibPolytopeBridge
import Kr25Ssmxt.Model.Program
import ArlibCommunity.Algorithms.HitAndRun.Analysis.Background.Arlib.Lattice.Rounding.RoundLaw
import ArlibCommunity.Algorithms.HitAndRun.Analysis.Background.Arlib.MarkovChains.Continuous.PointwiseRoute

/-!
# Integer randomized-rounding output and TTC coded lattice points

KV97 rounds a continuous point to `Z^n`.  TTC records the same vector together with its
decimal precision.  This file proves that the accepted integer vectors in the scaled body
are exactly TTC's `codedLatticePoints`.
-/

noncomputable section

namespace Arlib.KV97

open MeasureTheory ProbabilityTheory
open Arlib.Lattice.Rounding

theorem isProbabilityMeasure_roundedMeasureLaw {n : Nat}
    (mu : Measure (EuclideanSpace Real (Fin n))) [IsProbabilityMeasure mu] :
    IsProbabilityMeasure (Kr25Ssmxt.kv97RoundedMeasureLaw mu) := by
  unfold Kr25Ssmxt.kv97RoundedMeasureLaw
  infer_instance

theorem roundedMeasureLaw_singleton {n : Nat}
    (mu : Measure (EuclideanSpace Real (Fin n))) (z : Fin n → Int) :
    Kr25Ssmxt.kv97RoundedMeasureLaw mu {z} =
      ∫⁻ p, ENNReal.ofReal (prodTent (Kr25Ssmxt.kv97LatEmb n z) p) ∂mu := by
  rw [Kr25Ssmxt.kv97RoundedMeasureLaw,
    Measure.bind_apply (by measurability) (Kr25Ssmxt.kv97RoundingKernel n).aemeasurable]
  apply lintegral_congr
  intro p
  change roundLaw (WithLp.ofLp p) {z} = _
  rw [roundLaw_singleton]
  rfl

theorem roundedMeasureLaw_singleton_real {n : Nat}
    (mu : Measure (EuclideanSpace Real (Fin n))) [IsProbabilityMeasure mu]
    (z : Fin n → Int) :
    (Kr25Ssmxt.kv97RoundedMeasureLaw mu).real {z} =
      ∫ p, prodTent (Kr25Ssmxt.kv97LatEmb n z) p ∂mu := by
  have hint : Integrable (prodTent (Kr25Ssmxt.kv97LatEmb n z)) mu :=
    Arlib.integrable_of_forall_mem_Icc (measurable_prodTent _)
      (fun p => prodTent_nonneg _ p) (fun p => Arlib.PointwiseRoute.prodTent_le_one _ p)
  have hnn : 0 ≤ᵐ[mu] prodTent (Kr25Ssmxt.kv97LatEmb n z) :=
    Filter.Eventually.of_forall fun p => prodTent_nonneg _ p
  rw [Measure.real, roundedMeasureLaw_singleton,
    ← ofReal_integral_eq_lintegral_ofReal hint hnn,
    ENNReal.toReal_ofReal (integral_nonneg fun p => prodTent_nonneg _ p)]

theorem roundedMeasureLaw_real_finite {n : Nat}
    (mu : Measure (EuclideanSpace Real (Fin n))) [IsProbabilityMeasure mu]
    (T : Set (Fin n → Int)) [Fintype T] (hT : T.Finite) :
    (Kr25Ssmxt.kv97RoundedMeasureLaw mu).real T =
      ∑ z : T, ∫ p, prodTent (Kr25Ssmxt.kv97LatEmb n z.1) p ∂mu := by
  classical
  letI : IsProbabilityMeasure (Kr25Ssmxt.kv97RoundedMeasureLaw mu) :=
    isProbabilityMeasure_roundedMeasureLaw mu
  calc
    (Kr25Ssmxt.kv97RoundedMeasureLaw mu).real T =
        (Kr25Ssmxt.kv97RoundedMeasureLaw mu).real (hT.toFinset : Set (Fin n → Int)) := by
          rw [hT.coe_toFinset]
    _ = ∑ z ∈ hT.toFinset, (Kr25Ssmxt.kv97RoundedMeasureLaw mu).real {z} := by
      symm
      exact sum_measureReal_singleton hT.toFinset
    _ = ∑ z : T, (Kr25Ssmxt.kv97RoundedMeasureLaw mu).real {z.1} := by
      exact Finset.sum_subtype hT.toFinset (fun z => hT.mem_toFinset) _
    _ = ∑ z : T, ∫ p, prodTent (Kr25Ssmxt.kv97LatEmb n z.1) p ∂mu := by
      apply Finset.sum_congr rfl
      intro z _
      exact roundedMeasureLaw_singleton_real mu z.1

end Arlib.KV97

namespace Kr25Ssmxt

open Set MeasureTheory ProbabilityTheory

lemma encodeInteger_injective {n : Nat} (b : Nat) :
    Function.Injective (encodeInteger (n := n) b) := by
  intro z w h
  exact congrArg Prod.snd h

lemma scaled_toPoint_encodeInteger {n : Nat} (b : Nat) (z : Fin n → Int) :
    decimalScale b • toEuclidean (encodeInteger b z).toPoint = kv97LatEmb n z := by
  ext i
  change decimalScale b * ((z i : Real) / decimalScale b) = (z i : Real)
  exact mul_div_cancel₀ _ (decimalScale_ne_zero b)

/-- Acceptance after scaling is the same predicate as membership in TTC's coded set. -/
theorem encodeInteger_mem_coded_iff {n : Nat} (P : PolytopeData n) (b : Nat)
    (z : Fin n → Int) :
    encodeInteger b z ∈ codedLatticePoints P b ↔ z ∈ acceptedIntegers P b := by
  change ((encodeInteger b z).1 = b ∧ (encodeInteger b z).toPoint ∈ P.carrier) ↔ _
  simp only [encodeInteger, true_and]
  rw [acceptedIntegers, Set.mem_setOf_eq, ← P.image_decimalScale_eq_scaledBody b]
  constructor
  · intro hz
    exact ⟨(encodeInteger b z).toPoint, hz, scaled_toPoint_encodeInteger b z⟩
  · rintro ⟨x, hx, hxeq⟩
    have hpoint : x = (encodeInteger b z).toPoint := by
      ext i
      have hi := congrArg (fun y : EuclideanSpace Real (Fin n) => y i) hxeq
      change decimalScale b * x i = (z i : Real) at hi
      change x i = (z i : Real) / (10 : Real) ^ b
      rw [show (10 : Real) ^ b = decimalScale b by rfl, eq_div_iff (decimalScale_ne_zero b)]
      simpa [mul_comm] using hi
    change (encodeInteger b z).toPoint ∈ P.carrier
    rw [← hpoint]
    exact hx

/-- The accepted KV97 integer vectors map onto exactly the TTC coded lattice set. -/
theorem image_encodeInteger_acceptedIntegers {n : Nat} (P : PolytopeData n) (b : Nat) :
    encodeInteger b '' acceptedIntegers P b = codedLatticePoints P b := by
  ext x
  constructor
  · rintro ⟨z, hz, rfl⟩
    exact (encodeInteger_mem_coded_iff P b z).2 hz
  · intro hx
    have hxe : encodeInteger b x.2 = x := Prod.ext hx.1.symm rfl
    refine ⟨x.2, ?_, hxe⟩
    rw [← encodeInteger_mem_coded_iff P b x.2, hxe]
    exact hx

/-- Once the per-integer normalized weight window has been proved, the concrete
round--reject--encode law satisfies TTC's pointwise almost-uniform interface. -/
theorem acceptedRoundedLatticeLaw_almostUniform_of_ratio {n : Nat}
    (mu : Measure (EuclideanSpace Real (Fin n))) [IsProbabilityMeasure mu]
    (P : PolytopeData n) (b : Nat) {eta : Real}
    (hfinite : (codedLatticePoints P b).Finite)
    (hnonempty : (codedLatticePoints P b).Nonempty)
    (haccept : kv97RoundedMeasureLaw mu (acceptedIntegers P b) ≠ 0)
    (hratio : ∀ z ∈ acceptedIntegers P b,
      (kv97RoundedMeasureLaw mu).real {z} /
          (kv97RoundedMeasureLaw mu).real (acceptedIntegers P b) ∈
        Arlib.relErr eta (1 / (codedLatticePoints P b).ncard)) :
    AlmostUniformPointwise (acceptedRoundedLatticeLaw mu P b)
      (codedLatticePoints P b) eta := by
  let mur := kv97RoundedMeasureLaw mu
  have hmur : IsProbabilityMeasure mur :=
    Arlib.KV97.isProbabilityMeasure_roundedMeasureLaw mu
  letI : IsProbabilityMeasure mur := hmur
  have hacceptTop : mur (acceptedIntegers P b) ≠ ⊤ := measure_ne_top _ _
  have hcond : IsProbabilityMeasure (Arlib.condOn mur (acceptedIntegers P b)) :=
    Arlib.isProbabilityMeasure_condOn mur haccept hacceptTop
  letI : IsProbabilityMeasure (Arlib.condOn mur (acceptedIntegers P b)) := hcond
  refine ⟨?_, hfinite, hnonempty, ?_, ?_⟩
  · exact Measure.isProbabilityMeasure_map (by fun_prop)
  · rw [acceptedRoundedLatticeLaw, Measure.map_apply (by fun_prop) (by measurability)]
    have hpre : encodeInteger b ⁻¹' (codedLatticePoints P b)ᶜ ⊆
        (acceptedIntegers P b)ᶜ := by
      intro z hz hza
      exact hz ((encodeInteger_mem_coded_iff P b z).2 hza)
    exact measure_mono_null hpre
      (Arlib.condOn_compl_eq_zero mur (by measurability))
  · intro x hx
    have hxb : x.1 = b := hx.1
    have hxe : encodeInteger b x.2 = x := Prod.ext hxb.symm rfl
    have hxacc : x.2 ∈ acceptedIntegers P b := by
      rw [← encodeInteger_mem_coded_iff P b x.2, hxe]
      exact hx
    have hpre : encodeInteger b ⁻¹' ({x} : Set (LatticePoint n)) = {x.2} := by
      ext z
      simp only [Set.mem_preimage, Set.mem_singleton_iff]
      constructor
      · intro hz
        exact congrArg Prod.snd hz
      · intro hz
        simpa [hz] using hxe
    rw [acceptedRoundedLatticeLaw, Measure.real, Measure.map_apply (by fun_prop) (by measurability),
      hpre, Arlib.condOn_apply mur (by measurability) (by measurability),
      Set.inter_eq_left.2 (Set.singleton_subset_iff.2 hxacc), ENNReal.toReal_div]
    simpa [mur, Measure.real] using hratio x.2 hxacc

end Kr25Ssmxt

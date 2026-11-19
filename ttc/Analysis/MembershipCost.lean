import ttc.Analysis.ScaledBody
import ttc.Analysis.ChebyshevCenter

/-! # The membership test: correctness and cost

`HalfspacePresentation.memberProg` (`Model/Prelude.lean`) answers `x ∈ P` exactly, and
spends exactly `2 n r` arithmetic operations (`facetScanOperations n r`) when `n ≥ 1`.

The charged algorithm reads its membership charges off this program. The last section turns
them into the closed forms used by the runtime proofs. -/

namespace ttc

/-- `2 n r`: the cost of one membership test in a polytope with `r` facets (proved below). -/
def TTCRuntime.facetScanOperations (dimension facets : Nat) : Nat := 2 * dimension * facets

namespace Counted

@[simp] theorem andThen_value {α β : Type} (m : Counted α) (f : α → Counted β) :
    (m.andThen f).value = (f m.value).value := rfl

@[simp] theorem andThen_cost {α β : Type} (m : Counted α) (f : α → Counted β) :
    (m.andThen f).cost = m.cost + (f m.value).cost := rfl

@[simp] theorem bind_eq {α β : Type} (m : Counted α) (f : α → Counted β) :
    m >>= f = m.andThen f := rfl

@[simp] theorem pure_value {α : Type} (a : α) : (Counted.pure a).value = a := rfl
@[simp] theorem pure_cost {α : Type} (a : α) : (Counted.pure a).cost = 0 := rfl

/-- The dot-product program computes the dot product. -/
theorem dot_value : ∀ (n : Nat) (a x : Fin n → Real), (dot n a x).value = dotProduct a x
  | 0, a, x => by simp [dot, dotProduct]
  | 1, a, x => by simp [dot, mul, dotProduct]
  | n + 2, a, x => by
      simp only [dot, bind_eq, andThen_value, add, mul, dot_value (n + 1)]
      conv_rhs => rw [dotProduct, Fin.sum_univ_succ]
      rfl

/-- The dot product in dimension `n + 1` costs `2n + 1` operations. -/
theorem dot_cost : ∀ (n : Nat) (a x : Fin (n + 1) → Real), (dot (n + 1) a x).cost = 2 * n + 1
  | 0, a, x => by simp [dot, mul]
  | n + 1, a, x => by
      simp only [dot, bind_eq, andThen_cost, add, mul, dot_cost n]
      omega

open Classical in
/-- The facet loop answers whether every facet inequality holds. -/
theorem allFacets_value {n : Nat} : ∀ (r : Nat) (a : Fin r → Point n) (b : Fin r → Real)
    (x : Point n), (allFacets r a b x).value = true ↔ ∀ j, dotProduct (a j) x ≤ b j
  | 0, a, b, x => by simp [allFacets]
  | r + 1, a, b, x => by
      simp only [allFacets, bind_eq, andThen_value, pure_value, le, Bool.and_eq_true,
        decide_eq_true_eq, dot_value, allFacets_value r, Fin.forall_fin_succ]
      rfl

/-- The facet loop over `r` facets in dimension `n ≥ 1` costs `2 n r` operations. -/
theorem allFacets_cost {n : Nat} (hn : 0 < n) : ∀ (r : Nat) (a : Fin r → Point n)
    (b : Fin r → Real) (x : Point n), (allFacets r a b x).cost = 2 * n * r
  | 0, a, b, x => by simp [allFacets]
  | r + 1, a, b, x => by
      obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_lt hn
      simp only [allFacets, bind_eq, andThen_cost, pure_cost, le,
        allFacets_cost hn r, zero_add]
      rw [show m + 1 = 0 + m + 1 by omega, dot_cost]
      ring

end Counted

/-- **Correctness.** The membership program answers `true` exactly when `x ∈ P`. -/
theorem HalfspacePresentation.memberProg_correct {n : Nat} (H : HalfspacePresentation n)
    (x : Point n) : (H.memberProg x).value = true ↔ x ∈ H.carrier :=
  Counted.allFacets_value _ _ _ _

/-- **Cost.** The membership program costs exactly `facetScanOperations n r = 2 n r`. -/
theorem HalfspacePresentation.memberProg_cost {n : Nat} (hn : 0 < n)
    (H : HalfspacePresentation n) (x : Point n) :
    (H.memberProg x).cost = TTCRuntime.facetScanOperations n H.facetCount :=
  Counted.allFacets_cost hn _ _ _ _

/-- The worst-case cost `memberCost` is `2 n r` as well. -/
theorem HalfspacePresentation.memberCost_eq {n : Nat} (hn : 0 < n)
    (H : HalfspacePresentation n) :
    H.memberCost = TTCRuntime.facetScanOperations n H.facetCount := by
  simp only [HalfspacePresentation.memberCost, H.memberProg_cost hn, ciSup_const]

theorem HalfspacePresentation.memberProg_eq_false {n : Nat} (H : HalfspacePresentation n)
    (x : Point n) : (H.memberProg x).value = false ↔ x ∉ H.carrier := by
  rw [← H.memberProg_correct x]; simp

open Classical in
/-- The deletion pass removes exactly the copies whose point lies in `P`. -/
theorem TTCState.removeComponent_eq {n : Nat} (s : TTCState n) (P : PolytopeData n) :
    s.removeComponent P =
      { s with X := s.X.filter (fun copy => copy.2.toPoint ∉ P.carrier) } := by
  unfold TTCState.removeComponent
  congr 1
  apply Finset.filter_congr
  intro copy _
  exact P.presentation.memberProg_eq_false _

/-- `⟪a, x⟫` in arlib's Euclidean space is TTC's `dotProduct a x`. -/
theorem inner_toEuclidean {n : Nat} (a : Point n) (x : EuclideanSpace Real (Fin n)) :
    inner Real (toEuclidean a) x = dotProduct a (WithLp.ofLp x) := by
  simp [toEuclidean, PiLp.inner_apply, dotProduct, mul_comm]

/-- CV18's oracle answers membership in the normalized body. -/
theorem CommunityCV18.query_eq_true_iff {n : Nat} (P : PolytopeData n)
    (y : EuclideanSpace Real (Fin n)) :
    CommunityCV18.query P y = true ↔ y ∈ P.cv18Body := by
  have hγ := P.inradius_pos
  unfold CommunityCV18.query
  rw [HalfspacePresentation.memberProg_correct]
  simp only [HalfspacePresentation.carrier, PolytopeData.cv18Presentation, Set.mem_setOf_eq,
    PolytopeData.cv18Body, Set.mem_preimage, ArlibCommunity.Foundations.Convex.Polytope.body,
    PolytopeData.arlibNormal, inner_toEuclidean]
  refine forall_congr' fun j => ?_
  rw [le_div_iff₀ hγ]
  have hsplit : dotProduct (P.presentation.normal j)
      (WithLp.ofLp (P.inradius • y + toEuclidean P.incenter)) =
      P.inradius * dotProduct (P.presentation.normal j) (WithLp.ofLp y) +
        dotProduct (P.presentation.normal j) P.incenter := by
    simp [toEuclidean, dotProduct_add, dotProduct_smul]
  rw [hsplit]
  constructor <;> intro h <;> linarith

/-- The rejection test accepts exactly the integer points of `10^b · P`. -/
theorem acceptedIntegers_eq {n : Nat} (P : PolytopeData n) (b : Nat) :
    acceptedIntegers P b = {z | kv97LatEmb n z ∈ P.scaledBody b} := by
  ext z
  simp only [acceptedIntegers, Set.mem_setOf_eq, HalfspacePresentation.memberProg_correct,
    HalfspacePresentation.carrier, PolytopeData.scaledPresentation, PolytopeData.scaledBody,
    ArlibCommunity.Foundations.Convex.Polytope.body, PolytopeData.arlibNormal,
    inner_toEuclidean, kv97LatEmb]

/-! ## The membership charges in closed form -/

namespace TTCRuntime

/-- `queries` membership tests at `2 n r` each. -/
def membershipQueryOperations (dimension facets queries : Nat) : Nat :=
  facetScanOperations dimension facets * queries

/-- The rejection test is one membership test. -/
def rejectionTestOperations (dimension facets : Nat) : Nat :=
  facetScanOperations dimension facets

/-- The deletion pass: one membership test per stored copy, one operation per removal. -/
def deletionPassOperations (dimension facets checked removed : Nat) : Nat :=
  checked * facetScanOperations dimension facets +
    removed * deleteCopyOperations

/-- `4 n r + 4 r + 6 n + 9`: a bound on one Hit-and-Run step (`hitAndRunStepCost_le`). -/
def hitAndRunStepOperations (dimension facets : Nat) : Nat :=
  4 * dimension * facets + 4 * facets + 6 * dimension + 9

/-- One sampler attempt: start point, the walk, rounding, and the rejection test. -/
def samplingAttemptOperations (dimension facets steps : Nat) : Nat :=
  ballStartOperations dimension + steps * hitAndRunStepOperations dimension facets +
    roundPointOperations dimension + rejectionTestOperations dimension facets

end TTCRuntime

/-- The deletion pass's charge, in closed form. -/
theorem TTCState.deletionCost_eq {n : Nat} (hn : 0 < n) (s : TTCState n)
    (P : PolytopeData n) :
    s.deletionCost P = TTCRuntime.deletionPassOperations n P.presentation.facetCount
      s.X.card (s.X.card - (s.removeComponent P).X.card) := by
  simp only [TTCState.deletionCost, TTCRuntime.deletionPassOperations,
    P.presentation.memberProg_cost hn, Finset.sum_const, smul_eq_mul]

/-- The charge for `q` CV18 queries, in closed form. -/
theorem PolytopeData.cv18QueryCost_eq {n : Nat} (hn : 0 < n) (P : PolytopeData n)
    (q : Nat) :
    P.cv18Presentation.memberCost * q =
      TTCRuntime.membershipQueryOperations n P.presentation.facetCount q := by
  rw [HalfspacePresentation.memberCost_eq hn]
  rfl

end ttc

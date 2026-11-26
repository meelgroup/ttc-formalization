import ttc.Analysis.LegacyRun

/-! The decimal-scaled component and the integer lattice in arlib's Euclidean space, used by
the analysis of the rejection test. -/

noncomputable section

namespace ttc

/-! ## The offsets as formulas

The algorithm computes these offsets with the programs `scaledOffsetsProg` and
`hitAndRunOffsetsProg` (`Model/Run.lean`); `Analysis/MembershipCost.lean` proves the
programs compute exactly these formulas, which the analysis uses. -/

/-- Facet offsets of the decimal-dilated body. -/
def PolytopeData.scaledOffset {n : Nat} (P : PolytopeData n) (b : Nat) :
    Fin P.presentation.facetCount → Real :=
  fun i => decimalScale b * P.presentation.offset i

/-- The explicitly inflated offsets scanned by the finite-facet implementation. -/
def hitAndRunOffset {n : Nat} (P : PolytopeData n) (b : Nat) (eta : Real) :
    Fin P.presentation.facetCount → Real :=
  fun i => P.scaledOffset b i +
    ArlibCommunity.Algorithms.KV97.kappaOf (samplerC eta) (P.presentation.facetCount : Real) *
      ‖P.arlibNormal i‖

/-- Facet offsets after centering and dividing by the scaled inradius. -/
def PolytopeData.normalizedHitAndRunOffset {n : Nat} (P : PolytopeData n)
    (b : Nat) (eta : Real) : Fin P.presentation.facetCount → Real :=
  fun i =>
    (hitAndRunOffset P b eta i -
      inner Real (P.arlibNormal i) (P.scaledIncenter b)) / P.scaledInradius b

/-- The arlib body obtained by scaling every point of `P` by `10^b`. -/
def PolytopeData.scaledBody {n : Nat} (P : PolytopeData n) (b : Nat) :
    Set (EuclideanSpace Real (Fin n)) :=
  ArlibCommunity.Foundations.Convex.Polytope.body P.arlibNormal (P.scaledOffset b)

/-- The integer lattice embedded in arlib's Euclidean state space. -/
def kv97LatEmb (n : Nat) (z : Fin n → Int) : EuclideanSpace Real (Fin n) :=
  WithLp.toLp 2 fun i => (z i : Real)

end ttc

end

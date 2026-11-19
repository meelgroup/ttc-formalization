import ttc.Model.Run

/-! The decimal-scaled component and the integer lattice in arlib's Euclidean space, used by
the analysis of the rejection test. -/

namespace ttc

/-- The arlib body obtained by scaling every point of `P` by `10^b`. -/
def PolytopeData.scaledBody {n : Nat} (P : PolytopeData n) (b : Nat) :
    Set (EuclideanSpace Real (Fin n)) :=
  ArlibCommunity.Foundations.Convex.Polytope.body P.arlibNormal (P.scaledOffset b)

/-- The integer lattice embedded in arlib's Euclidean state space. -/
def kv97LatEmb (n : Nat) (z : Fin n → Int) : EuclideanSpace Real (Fin n) :=
  WithLp.toLp 2 fun i => (z i : Real)

end ttc

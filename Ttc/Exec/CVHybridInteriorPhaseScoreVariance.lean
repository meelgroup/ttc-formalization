import Ttc.Volume.CVHybridPhaseScoreVariance
import Arlib.Convexity.GaussianCooling.InteriorBridge

/-!
# Sharp hybrid phase variance for the measurable interior score

The public convex body may be nonmeasurable, whereas the executable score is cut off on
`interior K`.  Convexity makes the two cutoffs equal almost everywhere for volume, hence
also for every cooling law.  This file transports the sharp hybrid variance theorem across
that null-set bridge.
-/

set_option autoImplicit false

namespace Arlib.GaussianCooling

open MeasureTheory Metric Set

variable {n m i : Nat} {sigmaSq : Nat -> Real} {K : Set (EuclSpace n)}

theorem phaseScore_interior_ae_eq (hKc : Convex Real K) :
    phaseScore m sigmaSq (interior K) i =ᵐ[(volume : Measure (EuclSpace n))]
      phaseScore m sigmaSq K i := by
  classical
  filter_upwards [interior_ae_eq hKc] with x hx
  change (x ∈ interior K) = (x ∈ K) at hx
  unfold phaseScore
  rw [Set.indicator_apply, Set.indicator_apply, hx]

theorem coolLaw_absolutelyContinuous_volume :
    coolLaw m sigmaSq K i ≪ (volume : Measure (EuclSpace n)) := by
  exact (withDensity_absolutelyContinuous _ _).trans
    Measure.restrict_le_self.absolutelyContinuous

theorem integral_phaseScore_interior_eq (hKc : Convex Real K) :
    ∫ x, phaseScore m sigmaSq (interior K) i x ∂coolLaw m sigmaSq K i =
      ∫ x, phaseScore m sigmaSq K i x ∂coolLaw m sigmaSq K i := by
  apply integral_congr_ae
  exact coolLaw_absolutelyContinuous_volume.ae_eq (phaseScore_interior_ae_eq hKc)

theorem integral_phaseScore_interior_sq_eq (hKc : Convex Real K) :
    ∫ x, phaseScore m sigmaSq (interior K) i x ^ 2 ∂coolLaw m sigmaSq K i =
      ∫ x, phaseScore m sigmaSq K i x ^ 2 ∂coolLaw m sigmaSq K i := by
  apply integral_congr_ae
  filter_upwards [coolLaw_absolutelyContinuous_volume.ae_eq
    (phaseScore_interior_ae_eq hKc)] with x hx
  rw [hx]

end Arlib.GaussianCooling

namespace Ttc.CVHybridSchedule

open MeasureTheory Metric Set
open Arlib.GaussianCooling
open Arlib.GaussianCooling.Chunked

/-- The sharp source factor for the executable, measurable `interior K` score. -/
theorem phaseScore_interior_sq_moment_le {n J : Nat} (hn : 3 <= n)
    {K : Set (EuclSpace n)} (hKc : Convex Real K) (hKcl : IsClosed K)
    (hKb : Bornology.IsBounded K) (hvol : 0 < volume K)
    (hball : ball (0 : EuclSpace n) 1 ⊆ K) (hfin : volume K ≠ ⊤)
    {C s0 : Real} (hC : 0 < C) (hs0 : 0 < s0)
    (hbelow : ∀ j < J,
      adaptiveChunkStart (C ^ 2 * n) (coldEnd n s0) j <= C ^ 2 * n)
    (hKR : K ⊆ closedBall 0 (C * Real.sqrt n))
    (i : Fin (coldPhases n s0 +
      adaptiveChunkOffset (C ^ 2 * n) (coldEnd n s0) J)) :
    let phases := coldPhases n s0 +
      adaptiveChunkOffset (C ^ 2 * n) (coldEnd n s0) J
    let sched := sigmaSq n (C ^ 2 * n) s0
    ∫ x, phaseScore (phases + 1) sched (interior K) i x ^ 2
        ∂(coolLaw (phases + 1) sched K i) <=
      phaseVarFactor n 1 (C ^ 2 * n) s0 i *
        (∫ x, phaseScore (phases + 1) sched (interior K) i x
          ∂(coolLaw (phases + 1) sched K i)) ^ 2 := by
  dsimp only
  rw [integral_phaseScore_interior_sq_eq hKc,
    integral_phaseScore_interior_eq hKc]
  exact phaseScore_sq_moment_le hn hKc hKcl hKb hvol hball hfin hC hs0
    hbelow hKR i

end Ttc.CVHybridSchedule

#print axioms Arlib.GaussianCooling.phaseScore_interior_ae_eq
#print axioms Arlib.GaussianCooling.coolLaw_absolutelyContinuous_volume
#print axioms Ttc.CVHybridSchedule.phaseScore_interior_sq_moment_le

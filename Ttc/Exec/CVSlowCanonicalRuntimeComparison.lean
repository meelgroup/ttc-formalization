import Ttc.Exec.CVSlowCanonicalDeadlineCost
import Ttc.Exec.CVHotRefreshHonestRuntime
import Ttc.Exec.CVSourceTheorem11Arithmetic

/-!
# Explicit slow-canonical runtime comparison

This file removes the last opaque `T,L` scalar from the slow canonical certificate.
The resulting public shape is the capped radial-log shape multiplied by the displayed
slow-schedule overhead.  The multiplier is intentionally explicit: the uniformly slow
schedule is a correctness route, not the faster CV schedule from the paper.
-/

set_option autoImplicit false

namespace Ttc.CVSlowCanonicalRuntimeComparison

open Ttc.CVSlowCanonicalDeadlineCost Ttc.CVSlowCanonicalShareBounds
open Ttc.CVHotRefreshHonestRuntime Ttc.CVSourceTheorem11Arithmetic
open Ttc.CVSourcePolynomialCutoffCapstone

/-- Real upper envelope for the literal natural retry cap. -/
noncomputable def slowCanonicalRetryRealEnvelope
    (m k : Nat) (eps R s0 : Real) : Real :=
  16 * (Real.logb 2 (1 / slowCanonicalShareFloor m k eps R s0) + 1)

/-- Real upper envelope for the literal natural mixing deadline. -/
noncomputable def slowCanonicalDeadlineRealEnvelope
    (n m k : Nat) (eps R s0 N : Real) : Real :=
  4 * 640 ^ 2 * slowCanonicalGeometryEnvelope n m k eps N *
      slowCanonicalDeadlinePayload m k eps R s0 / Real.log 2 ^ 2 + 3

/-- Exact explicit overhead paid by all streams and phases of one slow run. -/
noncomputable def slowCanonicalRetainedRealEnvelope
    (n m k : Nat) (eps R s0 N : Real) : Real :=
  (k : Real) * (m : Real) * 10 *
    slowCanonicalRetryRealEnvelope m k eps R s0 *
    slowCanonicalDeadlineRealEnvelope n m k eps R s0 N *
    (2 * Real.exp 1)

theorem slowCanonicalRetriesCap_cast_le_realEnvelope
    {m k : Nat} {eps R s0 : Real}
    (heps : 0 < eps) (heps1 : eps ≤ 1) (hs0 : 0 < s0) :
    (slowCanonicalRetriesCap m k eps R s0 : Real) ≤
      slowCanonicalRetryRealEnvelope m k eps R s0 := by
  have hf0 := slowCanonicalShareFloor_pos
    (m := m) (k := k) (R := R) heps hs0
  have hf1 := slowCanonicalShareFloor_lt_one
    (m := m) (k := k) (R := R) (s0 := s0) heps heps1
  have hindex := Ttc.CVAdaptive.explicitDyadicTailIndex_lt_logb_add_one hf0 hf1
  unfold slowCanonicalRetriesCap slowCanonicalRetryRealEnvelope
  push_cast
  linarith

theorem slowCanonicalDeadlineCap_cast_le_realEnvelope
    {n m k : Nat} {eps R s0 N : Real}
    (hgeom0 : 0 ≤ slowCanonicalGeometryEnvelope n m k eps N)
    (hpayload0 : 0 ≤ slowCanonicalDeadlinePayload m k eps R s0) :
    (slowCanonicalDeadlineCap n m k eps R s0 N : Real) ≤
      slowCanonicalDeadlineRealEnvelope n m k eps R s0 N := by
  let x := 4 * 640 ^ 2 * slowCanonicalGeometryEnvelope n m k eps N *
      slowCanonicalDeadlinePayload m k eps R s0 / Real.log 2 ^ 2 + 1
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hx0 : 0 ≤ x := by
    dsimp only [x]
    positivity
  have hceil := (Nat.ceil_lt_add_one hx0).le
  unfold slowCanonicalDeadlineCap slowCanonicalDeadlineRealEnvelope
  dsimp only [x] at hceil
  push_cast
  linarith

theorem slowCanonicalRetainedScalar_le_realEnvelope
    {n m k : Nat} {eps R s0 N : Real}
    (heps : 0 < eps) (heps1 : eps ≤ 1) (hs0 : 0 < s0)
    (hgeom0 : 0 ≤ slowCanonicalGeometryEnvelope n m k eps N)
    (hpayload0 : 0 ≤ slowCanonicalDeadlinePayload m k eps R s0) :
    (k : Real) * (m : Real) *
        (10 * (slowCanonicalRetriesCap m k eps R s0 : Real) *
          (slowCanonicalDeadlineCap n m k eps R s0 N : Real) *
          (2 * Real.exp 1)) ≤
      slowCanonicalRetainedRealEnvelope n m k eps R s0 N := by
  have hL := slowCanonicalRetriesCap_cast_le_realEnvelope
    (m := m) (k := k) (R := R) heps heps1 hs0
  have hT := slowCanonicalDeadlineCap_cast_le_realEnvelope
    (n := n) (m := m) (k := k) (eps := eps) (R := R) (s0 := s0) (N := N)
    hgeom0 hpayload0
  have hL0 : 0 ≤ slowCanonicalRetryRealEnvelope m k eps R s0 :=
    (by positivity : (0 : Real) ≤ slowCanonicalRetriesCap m k eps R s0) |>.trans hL
  have hT0 : 0 ≤ slowCanonicalDeadlineRealEnvelope n m k eps R s0 N :=
    (by positivity : (0 : Real) ≤ slowCanonicalDeadlineCap n m k eps R s0 N) |>.trans hT
  unfold slowCanonicalRetainedRealEnvelope
  calc
    _ = (k : Real) * (m : Real) * 10 *
        (slowCanonicalRetriesCap m k eps R s0 : Real) *
        (slowCanonicalDeadlineCap n m k eps R s0 N : Real) *
        (2 * Real.exp 1) := by ring
    _ ≤ (k : Real) * (m : Real) * 10 *
        slowCanonicalRetryRealEnvelope m k eps R s0 *
        (slowCanonicalDeadlineCap n m k eps R s0 N : Real) *
        (2 * Real.exp 1) := by gcongr
    _ ≤ (k : Real) * (m : Real) * 10 *
        slowCanonicalRetryRealEnvelope m k eps R s0 *
        slowCanonicalDeadlineRealEnvelope n m k eps R s0 N *
        (2 * Real.exp 1) := by gcongr

/-- Honest public runtime shape for the slow correctness route. -/
noncomputable def cvSlowCanonicalCappedRadialShape
    (n m k : Nat) (R2 eps p s0 N : Real) : Real :=
  cvCappedRadialLogComplexityShapeClipped n R2 eps p *
    max 1 (slowCanonicalRetainedRealEnvelope n m k eps (Real.sqrt R2) s0 N)

theorem one_le_cvCappedRadialLogComplexityShapeClipped
    {n : Nat} (hn : 1 ≤ n) {R2 eps p : Real}
    (hR2 : 0 ≤ R2) (heps : 0 < eps) (heps1 : eps < 1) :
    1 ≤ cvCappedRadialLogComplexityShapeClipped n R2 eps p := by
  have hbase := one_le_cvBaseClipped hn hR2 heps heps1
  have hp : 1 ≤ max 1 (Real.log (1 / p)) := le_max_left _ _
  have hrad : 1 ≤ sourceLogFactor (max 1 R2) ^ 2 := by
    unfold sourceLogFactor
    nlinarith [le_max_left (1 : Real) (Real.log (max 1 R2))]
  have hnmax : 1 ≤ max 1 (n : Real) := le_max_left _ _
  unfold cvCappedRadialLogComplexityShapeClipped
    Ttc.CVRadialLogEnvelope.cvRadialLogComplexityShapeClipped
    Ttc.cvComplexityShapeClipped
  change 1 ≤
    (((max (R2 * (n : Real) ^ 2) ((n : Real) ^ 3) / eps ^ 2) *
      max 1 (Real.log n) ^ 2 * max 1 (Real.log (1 / eps)) ^ 2 *
      max 1 (Real.log ((n : Real) / eps)) ^ 2) *
      max 1 (Real.log (1 / p))) * sourceLogFactor (max 1 R2) ^ 2 *
      max 1 (n : Real)
  have h0 : 0 ≤
      (max (R2 * (n : Real) ^ 2) ((n : Real) ^ 3) / eps ^ 2) *
      max 1 (Real.log n) ^ 2 * max 1 (Real.log (1 / eps)) ^ 2 *
      max 1 (Real.log ((n : Real) / eps)) ^ 2 := zero_le_one.trans hbase
  calc
    1 ≤ (max (R2 * (n : Real) ^ 2) ((n : Real) ^ 3) / eps ^ 2) *
        max 1 (Real.log n) ^ 2 * max 1 (Real.log (1 / eps)) ^ 2 *
        max 1 (Real.log ((n : Real) / eps)) ^ 2 := hbase
    _ ≤ ((max (R2 * (n : Real) ^ 2) ((n : Real) ^ 3) / eps ^ 2) *
        max 1 (Real.log n) ^ 2 * max 1 (Real.log (1 / eps)) ^ 2 *
        max 1 (Real.log ((n : Real) / eps)) ^ 2) *
        max 1 (Real.log (1 / p)) := le_mul_of_one_le_right h0 hp
    _ ≤ (((max (R2 * (n : Real) ^ 2) ((n : Real) ^ 3) / eps ^ 2) *
        max 1 (Real.log n) ^ 2 * max 1 (Real.log (1 / eps)) ^ 2 *
        max 1 (Real.log ((n : Real) / eps)) ^ 2) *
        max 1 (Real.log (1 / p))) * sourceLogFactor (max 1 R2) ^ 2 :=
      le_mul_of_one_le_right (by positivity) hrad
    _ ≤ _ := le_mul_of_one_le_right (by positivity) hnmax

/-- The exact retained scalar is absorbed by the honest slow public shape. -/
theorem slowCanonicalRetainedScalar_le_publicShape
    {n m k : Nat} (hn : 1 ≤ n) {R2 eps p s0 N : Real}
    (hR2 : 0 ≤ R2) (heps : 0 < eps) (heps1 : eps < 1)
    (hs0 : 0 < s0)
    (hgeom0 : 0 ≤ slowCanonicalGeometryEnvelope n m k eps N)
    (hpayload0 : 0 ≤ slowCanonicalDeadlinePayload m k eps (Real.sqrt R2) s0) :
    (k : Real) * (m : Real) *
        (10 * (slowCanonicalRetriesCap m k eps (Real.sqrt R2) s0 : Real) *
          (slowCanonicalDeadlineCap n m k eps (Real.sqrt R2) s0 N : Real) *
          (2 * Real.exp 1)) ≤
      cvSlowCanonicalCappedRadialShape n m k R2 eps p s0 N := by
  have hscalar := slowCanonicalRetainedScalar_le_realEnvelope
    (n := n) (m := m) (k := k) (eps := eps) (R := Real.sqrt R2)
    (s0 := s0) (N := N) heps heps1.le hs0 hgeom0 hpayload0
  have hshape := one_le_cvCappedRadialLogComplexityShapeClipped
    (p := p) hn hR2 heps heps1
  unfold cvSlowCanonicalCappedRadialShape
  calc
    _ ≤ slowCanonicalRetainedRealEnvelope n m k eps (Real.sqrt R2) s0 N := hscalar
    _ ≤ max 1 (slowCanonicalRetainedRealEnvelope n m k eps (Real.sqrt R2) s0 N) :=
      le_max_right _ _
    _ ≤ cvCappedRadialLogComplexityShapeClipped n R2 eps p *
        max 1 (slowCanonicalRetainedRealEnvelope n m k eps (Real.sqrt R2) s0 N) := by
      exact le_mul_of_one_le_left
        (zero_le_one.trans (le_max_left _ _)) hshape

/-- ENNReal form consumed directly by retained-history one-run certificates. -/
theorem slowCanonicalRetainedScalar_ennreal_le_publicShape
    {n m k : Nat} (hn : 1 ≤ n) {R2 eps p s0 N : Real}
    (hR2 : 0 ≤ R2) (heps : 0 < eps) (heps1 : eps < 1)
    (hs0 : 0 < s0)
    (hgeom0 : 0 ≤ slowCanonicalGeometryEnvelope n m k eps N)
    (hpayload0 : 0 ≤ slowCanonicalDeadlinePayload m k eps (Real.sqrt R2) s0) :
    (k : ENNReal) * (m : ENNReal) * ENNReal.ofReal
        (10 * (slowCanonicalRetriesCap m k eps (Real.sqrt R2) s0 : Real) *
          (slowCanonicalDeadlineCap n m k eps (Real.sqrt R2) s0 N : Real) *
          (2 * Real.exp 1)) ≤
      ENNReal.ofReal (cvSlowCanonicalCappedRadialShape n m k R2 eps p s0 N) := by
  have hreal := slowCanonicalRetainedScalar_le_publicShape
    (n := n) (m := m) (k := k) (p := p) hn hR2 heps heps1 hs0 hgeom0 hpayload0
  have hk0 : (0 : Real) ≤ k := by positivity
  have hm0 : (0 : Real) ≤ m := by positivity
  rw [← ENNReal.ofReal_natCast k, ← ENNReal.ofReal_natCast m,
    ← ENNReal.ofReal_mul hk0, ← ENNReal.ofReal_mul (mul_nonneg hk0 hm0)]
  exact ENNReal.ofReal_le_ofReal hreal

#print axioms slowCanonicalRetriesCap_cast_le_realEnvelope
#print axioms slowCanonicalDeadlineCap_cast_le_realEnvelope
#print axioms slowCanonicalRetainedScalar_le_realEnvelope
#print axioms slowCanonicalRetainedScalar_le_publicShape
#print axioms slowCanonicalRetainedScalar_ennreal_le_publicShape

end Ttc.CVSlowCanonicalRuntimeComparison

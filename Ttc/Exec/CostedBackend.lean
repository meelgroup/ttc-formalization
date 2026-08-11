/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import Ttc.Exec.Complexity

/-!
# Cost-certified oracle backends

This file is a downstream attachment point for executable oracle implementations.  It does
not change `Ttc.ttc`, and in particular does not pretend that the currently constructed
volume estimator or sampler has a polynomial running time.

`Ttc.CostedBackend` deliberately has two independent parts:

* `volume_correct` and `sample_correct` certify semantic predicates chosen by the caller;
* `volumeWork` and `sampleWork` are operational, per-cube charges, with proved uniform
  bounds `volumePrice` and `samplePrice`.

Thus a correctness theorem cannot silently serve as a cost theorem.  A future
Cousins--Vempala implementation and a future sampling implementation can share this
interface while using different correctness predicates and different notions of work.
-/

namespace Ttc

open MeasureTheory

variable {n : ℕ} {ι : Type*}

/-- An oracle bundle together with independent semantic and operational certificates.

The predicates are parameters rather than fields with hard-coded meanings.  This keeps the
interface usable both for `VolumeAlgorithm.correct`/a sampler TV theorem and for stronger
end-to-end specifications.  The work functions, unlike the semantic predicates, enter the
cost folded by `Ttc.runCostAt`. -/
structure CostedBackend (P : Params) (volumeSpec sampleSpec : Oracles n ι → Prop) where
  /-- The executable answers consumed by `Ttc.run`. -/
  oracles : Oracles n ι
  /-- Correctness of the volume part; independent of all work fields. -/
  volume_correct : volumeSpec oracles
  /-- Correctness of the sampling part; independent of all work fields. -/
  sample_correct : sampleSpec oracles
  /-- Operational work of one volume call at a cube. -/
  volumeWork : ι → ℕ
  /-- Operational work of producing one sample at a cube. -/
  sampleWork : ι → ℕ
  /-- A uniform, explicit volume-call price. -/
  volumePrice : ℕ
  /-- A uniform, explicit per-sample price. -/
  samplePrice : ℕ
  /-- The volume price is justified pointwise. -/
  volumeWork_le : ∀ i, volumeWork i ≤ volumePrice
  /-- The sample price is justified pointwise. -/
  sampleWork_le : ∀ i, sampleWork i ≤ samplePrice

namespace CostedBackend

variable {P : Params} {volumeSpec sampleSpec : Oracles n ι → Prop}

/-- The work charged to a run by a cost-certified backend. -/
noncomputable def runCost (B : CostedBackend P volumeSpec sampleSpec)
    (ρ : ℤ) (cubes : List ι) : ℕ :=
  Ttc.runCostAt P B.oracles B.volumeWork B.sampleWork ρ cubes

/-- Generic composition of pointwise oracle bounds through TTC's sample threshold. -/
theorem runCost_le (B : CostedBackend P volumeSpec sampleSpec) (ρ : ℤ)
    (cubes : List ι) (thr : ℕ) (hthr : P.thresh ≤ (thr : ℝ))
    (hterm : Terminates P B.oracles cubes) :
    B.runCost ρ cubes ≤
      cubes.length * (B.volumePrice + B.samplePrice * thr) := by
  exact runCostAt_le_uniform P B.oracles B.volumeWork B.sampleWork
    B.volumePrice B.samplePrice ρ cubes thr hthr hterm
    (fun i _ => B.volumeWork_le i) (fun i _ => B.sampleWork_le i)

end CostedBackend

section TtcBound

variable {A : Type*} {n : ℕ}
variable (atoms : A → LinAtom n) (φ : BForm A) (ε δ : ℝ)
variable (volumeSpec sampleSpec : Oracles n (Cube A) → Prop)

/-- A cost-certified backend's charge on TTC's own preprocessed cube list. -/
noncomputable def backendCost
    (B : CostedBackend (ttcBlock atoms φ ε δ) volumeSpec sampleSpec) : ℕ :=
  B.runCost (ttcPrec atoms φ ε δ) (toDNFd (ttcInput atoms φ))

/-- Explicit composition through TTC's threshold formula.

This is the theorem a polynomial volume implementation and a polynomial sampler should
instantiate.  It contains no asymptotic assertion: their concrete pointwise prices remain
visible as `B.volumePrice` and `B.samplePrice`, ready for a separate `IsBigO` corollary. -/
theorem backendCost_le_ttcComplexity
    (hε0 : 0 < ε) (hε1 : ε ≤ 1) (hn : 1 ≤ n) (hφ : φ.IsPositive)
    (hpos : 0 < volSol (atomSet atoms) φ) (hδ0 : 0 < δ) (hδ1 : δ ≤ 1)
    (B : CostedBackend (ttcBlock atoms φ ε δ) volumeSpec sampleSpec)
    (hterm : Terminates (ttcBlock atoms φ ε δ) B.oracles
      (toDNFd (ttcInput atoms φ))) :
    (backendCost atoms φ ε δ volumeSpec sampleSpec B : ℝ) ≤
      ttcComplexity atoms φ ε δ B.volumePrice B.samplePrice := by
  have hceil : ttcThresh atoms φ ε δ ≤ (⌈ttcThresh atoms φ ε δ⌉₊ : ℝ) :=
    Nat.le_ceil _
  have hnat := B.runCost_le (ttcPrec atoms φ ε δ)
    (toDNFd (ttcInput atoms φ)) ⌈ttcThresh atoms φ ε δ⌉₊ hceil hterm
  have hreal : (backendCost atoms φ ε δ volumeSpec sampleSpec B : ℝ) ≤
      ((toDNFd (ttcInput atoms φ)).length : ℝ) *
        ((B.volumePrice : ℝ) + (B.samplePrice : ℝ) *
          (⌈ttcThresh atoms φ ε δ⌉₊ : ℝ)) := by
    exact_mod_cast hnat
  rw [ttcInput_eq_preprocess] at hreal
  rw [ttcComplexity_def]
  refine le_trans hreal ?_
  have hceil_lt : (⌈ttcThresh atoms φ ε δ⌉₊ : ℝ) <
      ttcThresh atoms φ ε δ + 1 :=
    Nat.ceil_lt_add_one
      (ttcThresh_nonneg atoms φ ε δ hε0 hε1 hn hφ hpos hδ0 hδ1)
  have hthr := ttcThresh_le_sum atoms φ ε δ
    hε0 hε1 hn hφ hpos hδ0 hδ1
  have hprice : (⌈ttcThresh atoms φ ε δ⌉₊ : ℝ) ≤
      41472 * Real.log (30 / δ) / (ε ^ 2 * (12 - ε))
        + 15 * (Real.log (15 / (2 * δ))
            + Real.log ((toDNFd (preprocess atoms φ)).length)) + 1 := by
    linarith
  gcongr

end TtcBound

end Ttc

/-! ## Axiom profile -/

#print axioms Ttc.CostedBackend.runCost_le
#print axioms Ttc.backendCost_le_ttcComplexity

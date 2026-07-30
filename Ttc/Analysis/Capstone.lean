/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import Ttc.Model.ProblemSetting
import Ttc.Analysis.Decomposition

/-!
# The capstone: combining `lem:lattice` and `lem:numlattice`

The proof content behind `Model/Theorem`, in two layers.

**The deterministic core.** `Ttc.TtcAnalysis` is an internal bundle of the four
real numbers and four inequalities the arithmetic actually consumes — it is *not*
part of the audit surface, and `Ttc.TtcProb` (`Model/ProblemSetting`) does not extend
it. Over it we prove the paper's two chains:

* `(1−ε)·vol ≤ (1−ε)(1+ε/8)·L ≤ (1−ε/3)·L ≤ est`  (`Ttc.TtcAnalysis.le_est`)
* `est ≤ (1+ε/3)·L ≤ (1+ε)(1−ε/8)·L ≤ (1+ε)·vol`  (`Ttc.TtcAnalysis.est_le`)

so the `ε/8` of `lem:lattice` and the `ε/3` of `lem:numlattice` compose to the
`ε` of `thm:volumettc`, with slack.

**The bridge to the probabilistic statement.** `Ttc.TtcProb.toAnalysis` reads a
`Ttc.TtcAnalysis` off a `Ttc.TtcProb` at any sample point where `lem:numlattice`'s
conclusion holds, so the arithmetic is written once. `Model/Theorem` then applies
it pointwise and lets `measure_mono` carry the `1 − δ`.

**Non-vacuity.** `Ttc.trivialProb` inhabits `Ttc.TtcProb`, without which the
headline would be vacuously true. It is a *satisfiability* witness only — see
`AUDIT.md` §4.
-/

namespace Ttc

open MeasureTheory Set

/-! ## The deterministic core -/

/-- **The arithmetic interface.** The four quantities and four inequalities the
two-sided chain consumes, and nothing else. Internal: the audit surface is
`Ttc.TtcProb` (`Model/ProblemSetting`), whose fields subsume these. -/
structure TtcAnalysis (A : Type*) (n : ℕ) where
  /-- The multiplicative accuracy parameter. -/
  ε : ℝ
  /-- `ε` is positive. -/
  hε0 : 0 < ε
  /-- `ε` is at most one, as required by `thm:volumettc`. -/
  hε1 : ε ≤ 1
  /-- The interpretation of atoms as sets of points. -/
  M : A → Set (Space n)
  /-- The Boolean abstraction of the input formula. -/
  φ : BForm A
  /-- The normalised lattice count `|Q ∩ 𝕃ⁿ| / 10^(ρ·n)`. -/
  L : ℝ
  /-- A count is nonnegative. -/
  hL : 0 ≤ L
  /-- The estimate the algorithm outputs. -/
  est : ℝ
  /-- `lem:lattice`, lower half, at `η = ε/8`. -/
  lattice_lo : (1 - ε / 8) * L ≤ volSol M φ
  /-- `lem:lattice`, upper half, at `η = ε/8`. -/
  lattice_hi : volSol M φ ≤ (1 + ε / 8) * L
  /-- `lem:numlattice`, lower half. -/
  sketch_lo : (1 - ε / 3) * L ≤ est
  /-- `lem:numlattice`, upper half. -/
  sketch_hi : est ≤ (1 + ε / 3) * L

namespace TtcAnalysis

variable {A : Type*} {n : ℕ} (T : TtcAnalysis A n)

/-- **Lower bound.** `(1−ε)·vol ≤ (1−ε)(1+ε/8)·L ≤ (1−ε/3)·L ≤ est`. -/
theorem le_est : (1 - T.ε) * volSol T.M T.φ ≤ T.est := by
  have hv := T.lattice_hi
  have hL := T.hL
  have h0 := T.hε0
  have h1 := T.hε1
  have step1 : (1 - T.ε) * volSol T.M T.φ ≤ (1 - T.ε) * ((1 + T.ε / 8) * T.L) :=
    mul_le_mul_of_nonneg_left hv (by linarith)
  have harith : (1 - T.ε) * (1 + T.ε / 8) ≤ 1 - T.ε / 3 := by nlinarith
  have step2 : (1 - T.ε) * ((1 + T.ε / 8) * T.L) ≤ (1 - T.ε / 3) * T.L := by
    nlinarith [mul_le_mul_of_nonneg_right harith hL]
  linarith [T.sketch_lo]

/-- **Upper bound.** `est ≤ (1+ε/3)·L ≤ (1+ε)(1−ε/8)·L ≤ (1+ε)·vol`. -/
theorem est_le : T.est ≤ (1 + T.ε) * volSol T.M T.φ := by
  have hv := T.lattice_lo
  have hL := T.hL
  have h0 := T.hε0
  have h1 := T.hε1
  have harith : (1 + T.ε / 3) ≤ (1 + T.ε) * (1 - T.ε / 8) := by nlinarith
  have step1 : (1 + T.ε / 3) * T.L ≤ ((1 + T.ε) * (1 - T.ε / 8)) * T.L :=
    mul_le_mul_of_nonneg_right harith hL
  have step2 : ((1 + T.ε) * (1 - T.ε / 8)) * T.L ≤ (1 + T.ε) * volSol T.M T.φ := by
    have h := mul_le_mul_of_nonneg_left hv (by linarith : (0:ℝ) ≤ 1 + T.ε)
    linarith [h]
  linarith [T.sketch_hi]

/-- **The two-sided bound**, the deterministic content of `thm:volumettc`: the
`(1±ε/8)` of `lem:lattice` and the `(1±ε/3)` of `lem:numlattice` compose to
`(1±ε)`. -/
theorem volume_estimate : T.est ∈ relErr T.ε (volSol T.M T.φ) :=
  ⟨T.le_est, T.est_le⟩

end TtcAnalysis

/-- **`thm:decomposition` for a `Ttc.TtcProb`.** The set whose volume the headline
bounds is exactly the union of the polytopes the algorithm enumerates — the two
are the same set, not two things sharing a name. Proved from the `isDNF` field. -/
theorem TtcProb.sol_eq_union {A : Type*} {n : ℕ} (T : TtcProb A n) :
    ⋃ c ∈ T.D, region T.M c = sol T.M T.φ :=
  sol_eq_iUnion_region T.isDNF

/-! ## From the probabilistic bundle to the deterministic core -/

/-- **At a sample point where `lem:numlattice` holds, `T` gives a
`Ttc.TtcAnalysis`.** This is what lets `Model/Theorem` apply the arithmetic
pointwise without restating it. -/
noncomputable def TtcProb.toAnalysis {A : Type*} {n : ℕ} (T : TtcProb A n) {ω : T.Ω}
    (h : (1 - T.ε / 3) * T.L ≤ ttcOutput T.P T.O T.fuel T.ρ T.D ω ∧
         ttcOutput T.P T.O T.fuel T.ρ T.D ω ≤ (1 + T.ε / 3) * T.L) :
    TtcAnalysis A n where
  ε := T.ε
  hε0 := T.hε0
  hε1 := T.hε1
  M := T.M
  φ := T.φ
  L := T.L
  hL := T.hL
  est := ttcOutput T.P T.O T.fuel T.ρ T.D ω
  lattice_lo := T.lattice_lo
  lattice_hi := T.lattice_hi
  sketch_lo := h.1
  sketch_hi := h.2

/-! ## Non-vacuity

`Ttc.TtcProb.volume_estimate` (`Model/Theorem`) quantifies over `Ttc.TtcProb`; if
that structure were uninhabited the theorem would be vacuously true. The witness
below is *satisfiability* only — it says the fields are mutually consistent, not
that they hold of the real algorithm. That is `lem:numlattice`, which is assumed.
-/

/-- A degenerate oracle bundle: `Vol_ED` returns `1`, nothing is ever covered,
thinning is the identity, every Poisson draw is `0`, and `GenerateSamples`
returns `N` copies of the origin. It satisfies both constraints `Ttc.Oracles`
imposes. -/
def trivialOracles (n : ℕ) (ι : Type*) : Oracles n ι where
  vol := fun _ => 1
  covered := fun _ _ => false
  halve := id
  halve_card_le := fun _ => le_rfl
  pois := fun _ => 0
  gen := fun _ N _ => Multiset.replicate N 0
  gen_card := fun _ N _ => by simp

/-- A degenerate parameter block, to have some `Ttc.Params` to run at. -/
noncomputable def trivialParams : Params where
  ε := 1
  δ := 1
  n := 1
  m := 1
  r := 1
  hε0 := one_pos
  hε1 := le_rfl
  hn := le_rfl
  hm := le_rfl
  hr := le_rfl

/-- **A `Ttc.TtcProb` really exists.** The one-point sample space with the Dirac
measure, the degenerate oracle bundle, and the everywhere-false interpretation:
`Vol(F) = 0`, `L = 0`, and the algorithm outputs `0` — so `lem:numlattice`'s event
has probability `1`, and the witness holds even at `δ = 0`. -/
noncomputable def trivialProb {A : Type*} {n : ℕ} (a : A) : TtcProb A n where
  ε := 1
  δ := 0
  hε0 := one_pos
  hε1 := le_rfl
  M := fun _ => ∅
  φ := .atom a
  D := [[⟨a, true⟩]]
  isDNF := by intro v; simp [DNF.holds, Cube.holds, Lit.holds, BForm.holds]
  L := 0
  hL := le_rfl
  lattice_lo := by
    show (1 - (1:ℝ) / 8) * 0 ≤ volSol (fun _ => (∅ : Set (Space n))) (.atom a)
    simpa using volSol_nonneg (fun _ => (∅ : Set (Space n))) (.atom a)
  lattice_hi := by
    show volSol (fun _ => (∅ : Set (Space n))) (.atom a) ≤ (1 + (1:ℝ) / 8) * 0
    have hsol : sol (fun _ => (∅ : Set (Space n))) (.atom a) = ∅ := rfl
    simp [volSol, hsol]
  Ω := Unit
  mΩ := inferInstance
  μ := MeasureTheory.Measure.dirac ()
  isProb := inferInstance
  P := trivialParams
  O := fun _ => trivialOracles n (Cube A)
  fuel := 0
  gammaHat := 1
  ρ := trivialParams.precision 1
  rho_eq := rfl
  numlattice := by
    have hrun : ∀ u : Unit,
        ttcOutput trivialParams (fun _ => trivialOracles n (Cube A)) 0
            (trivialParams.precision 1) [[(⟨a, true⟩ : Lit A)]] u = 0 := by
      intro _
      simp [ttcOutput, run, step, dropCovered, trivialOracles]
    have hmem : () ∈ {ω : Unit | (1 - (1:ℝ) / 3) * 0 ≤
        ttcOutput trivialParams (fun _ => trivialOracles n (Cube A)) 0
            (trivialParams.precision 1) [[(⟨a, true⟩ : Lit A)]] ω ∧
        ttcOutput trivialParams (fun _ => trivialOracles n (Cube A)) 0
            (trivialParams.precision 1) [[(⟨a, true⟩ : Lit A)]] ω
          ≤ (1 + (1:ℝ) / 3) * 0} := by
      simp [hrun]
    rw [MeasureTheory.Measure.dirac_apply_of_mem hmem]
    norm_num

/-- `Ttc.TtcProb` is inhabited, so `Ttc.TtcProb.volume_estimate` is not vacuous. -/
theorem nonempty_ttcProb {A : Type*} {n : ℕ} (a : A) : Nonempty (TtcProb A n) :=
  ⟨trivialProb a⟩

end Ttc

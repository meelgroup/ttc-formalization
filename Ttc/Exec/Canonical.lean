/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import Ttc.TtcProb
import Ttc.Witness.BoxProb

/-!
# `Exec/Canonical`: the canonical probability space, built rather than assumed

`Ttc.TtcProb` carries its probability space as **fields** — `Ω`, `mΩ`, `μ`,
`isProb` — together with the oracle bundle `O` and the four fields that tie the
two together (`toTraj`, `toTraj_meas`, `law_eq`, `oracle_eq`).  A reader of
`Ttc.TtcProb.volume_estimate` therefore cannot see, from the statement, *what
space the probability is over*.  That is gap 3 of `END-TO-END-PLAN.md`'s
"THE ENDGOAL": the template
`ApproxNFA.approxNFA_countNFA` reads its space off `countNFAExec A n ε δ`, an
object **constructed** from the algorithm's inputs.

The construction is already in the development; it has simply never been factored
out.  `Ttc.trajLaw` (`Ttc/Coupling/Family.lean`) is the law of the coupled level
family on the trajectory space `ℕ → Fin L → ℕ`, `Ttc.isProbabilityMeasure_trajLaw`
says it is a probability measure, and `Ttc.trajOracles` is the oracle bundle that
reads a trajectory.  `Ttc.Box.boxProb` already instantiates exactly this.

`Ttc.canonicalTtcProb` below is the smart constructor: it takes the 48 fields that
genuinely have to be supplied — the geometry, the parameter block, the sampler and
the volume-oracle data — and fills in **ten** by construction:

| Field | Canonical value |
| --- | --- |
| `Ω` | `ℕ → Fin Lidx → ℕ`, the trajectory space |
| `mΩ` | `inferInstance` (the product σ-algebra) |
| `μ` | `Ttc.trajLaw θ` |
| `isProb` | `Ttc.isProbabilityMeasure_trajLaw θ` |
| `O` | `fun t => Ttc.trajOracles ptE_inj vol cover memPt t` |
| `toTraj` | `id` |
| `toTraj_meas` | `measurable_id.aemeasurable` |
| `law_eq` | `MeasureTheory.Measure.map_id` |
| `oracle_eq` | `fun _ => rfl` |
| `M`, `M_eq` | `fun a => (atoms a).halfspace`, `rfl` |

The last row is a bonus: the interpretation of the atoms is *determined* by the
atoms, so `M` need not be supplied beside `atoms` and `M_eq` need not be assumed.

**The faithfulness check.** A constructor the one existing witness cannot go
through is a constructor that has assumed something false, so
`Ttc.Box.boxProb_eq_canonical` proves that `Ttc.Box.boxProb` **is** this
constructor applied to the box's own data — by `rfl`, i.e. the two `TtcProb`s
agree field by field, definitionally.  `Witness/BoxProb.lean` is not touched.

**What is *not* discharged here.**  This file does not construct `P`, `ρ`, `θ`,
`vol`, `sampD`, `sampler`, `volAlg` or `volCoins`: those are the algorithm's
parameter block (step 4, `Ttc/Exec/Params.lean`) and its two oracles (Phases 3–5
of the plan).  It removes the *probability-space* gap only.
-/

namespace Ttc

open MeasureTheory Pointwise

section Canonical

variable {A : Type*} {n : ℕ}

/-- **The canonical `Ttc.TtcProb`.**

Every argument is data the algorithm genuinely has to be handed; the probability
space, its measure, the oracle bundle and the four fields linking them are
*constructed*, not assumed.  See the module docstring for the table.

The arguments are in dependency order, which differs slightly from the field order
of `Ttc.TtcProb`: `Lidx`, `ptE`, `ptE_inj`, `θ`, `vol`, `cover` and `memPt` all
precede `gen_mem`, because `gen_mem` is now a statement about the *constructed*
oracle bundle `Ttc.trajOracles` rather than about a free field `O`. -/
noncomputable def canonicalTtcProb
    -- the requested accuracy and confidence
    (ε δ : ℝ) (hε0 : 0 < ε) (hε1 : ε ≤ 1) (hδ0 : 0 < δ) (hδ1 : δ ≤ 1)
    -- the input formula and the AllSAT call
    (atoms : A → LinAtom n) (φ : BForm A) (toDNF : BForm A → DNF A)
    (isDNF : IsDNFOf (toDNF φ) φ) (isPositive : DNF.IsPositive (toDNF φ))
    -- the parameter block and its tie-backs
    (P : Params) (eps_eq : P.ε = ε) (delta_eq : P.δ = δ) (dim_eq : P.n = n)
    (cubes_le : (Nat.card {c : Cube A // c ∈ toDNF φ} : ℝ) ≤ P.m)
    (facets_le : (Nat.card (FacetIndex (toDNF φ)) : ℝ) ≤ P.r)
    (normal_ne_zero : ∀ j : FacetIndex (toDNF φ), 0 < ∑ k, (atoms j.2.val.atom).coeff k ^ 2)
    -- the geometry of the decomposition
    (cen : {c : Cube A // c ∈ toDNF φ} → Space n) (gammaHat : ℝ) (hgammaHat : 0 < gammaHat)
    (ball_subset : ∀ i, Metric.ball (cen i) gammaHat ⊆
      region (fun a => (atoms a).halfspace) i.val)
    (volume_ne_top : ∀ i : {c : Cube A // c ∈ toDNF φ},
      volume (region (fun a => (atoms a).halfspace) i.val) ≠ ⊤)
    -- the precision
    (ρ : ℤ) (rho_eq : ρ = P.precision gammaHat)
    -- the normalised lattice count
    (L : ℝ) (L_eq : L = normalisedCount (fun a => (atoms a).halfspace) φ ρ)
    -- the enumeration of `Sol(F) ∩ 𝕃ⁿ`
    (Lidx : ℕ) (ptE : Fin Lidx → Space n) (ptE_inj : Function.Injective ptE)
    (ptE_mem : ∀ s, ptE s ∈
      sol (fun a => (atoms a).halfspace) φ ∩ fineLattice n (latticeScale ρ))
    (ptE_onto : ∀ x ∈ sol (fun a => (atoms a).halfspace) φ ∩ fineLattice n (latticeScale ρ),
      ∃ s, ptE s = x)
    -- the rates, the volume estimates and the sampler
    (θ : Fin Lidx → ℝ) (vol : Cube A → ℝ) (sampD : Cube A → Space n → ℝ)
    (sampler : KV97Sampler A n (fun a => (atoms a).halfspace) (toDNF φ) ρ P.epsPrime sampD)
    (theta_eq : ∀ s, ∃ i, i ∈ toDNF φ ∧ ptE s ∈ region (fun a => (atoms a).halfspace) i ∧
      θ s = sampD i (ptE s) * vol i)
    -- the coverage test
    (cover : Space n → Cube A → Bool) (memPt : Cube A → Fin Lidx → Bool)
    (memPt_eq : ∀ i ∈ toDNF φ, ∀ s,
      memPt i s = true ↔ ptE s ∈ region (fun a => (atoms a).halfspace) i)
    (cover_eq : ∀ s i, cover (ptE s) i = memPt i s)
    -- `GenerateSamples` returns lattice points of the cube it was asked about
    (gen_mem : ∀ (t : ℕ → Fin Lidx → ℕ) (i : Cube A) (j N : ℕ), i ∈ toDNF φ →
      ∀ s ∈ (trajOracles ptE_inj vol cover memPt t).gen i j N ρ,
        s ∈ region (fun a => (atoms a).halfspace) i ∩ fineLattice n (latticeScale ρ))
    -- `Vol_ED`
    (volAlg : VolumeAlgorithm n) (volCoins : volAlg.Ω)
    (volED_eq : ∀ (i : Cube A) (hi : i ∈ toDNF φ), vol i =
      gammaHat ^ n * volAlg.est
        (roundBody (cen ⟨i, hi⟩) gammaHat (region (fun a => (atoms a).halfspace) i))
        P.epsPrime P.deltaPrime volCoins)
    (volCoins_good : ∀ i ∈ toDNF φ, vol i ∈
      relErr P.epsPrime (volume (region (fun a => (atoms a).halfspace) i)).toReal)
    (vol_pos : ∀ i ∈ toDNF φ, 0 < vol i)
    -- the instance is in the paper's regime
    (big : (1 - P.epsPrime) * P.thresh / 8 ≤ ∑ s, θ s) :
    TtcProb A n where
  ε := ε
  δ := δ
  hε0 := hε0
  hε1 := hε1
  hδ0 := hδ0
  hδ1 := hδ1
  atoms := atoms
  -- **constructed**: the interpretation is the one the linear atoms denote.
  M := fun a => (atoms a).halfspace
  M_eq := rfl
  φ := φ
  toDNF := toDNF
  isDNF := isDNF
  isPositive := isPositive
  -- **constructed**: the trajectory space of the coupled level family.
  Ω := ℕ → Fin Lidx → ℕ
  mΩ := inferInstance
  μ := trajLaw θ
  isProb := isProbabilityMeasure_trajLaw θ
  P := P
  eps_eq := eps_eq
  delta_eq := delta_eq
  dim_eq := dim_eq
  cubes_le := cubes_le
  facets_le := facets_le
  normal_ne_zero := normal_ne_zero
  -- **constructed**: the oracles read the family.
  O := fun t => trajOracles ptE_inj vol cover memPt t
  cen := cen
  gammaHat := gammaHat
  hgammaHat := hgammaHat
  ball_subset := ball_subset
  volume_ne_top := volume_ne_top
  ρ := ρ
  rho_eq := rho_eq
  gen_mem := gen_mem
  L := L
  L_eq := L_eq
  Lidx := Lidx
  ptE := ptE
  ptE_inj := ptE_inj
  ptE_mem := ptE_mem
  ptE_onto := ptE_onto
  θ := θ
  vol := vol
  sampD := sampD
  sampler := sampler
  theta_eq := theta_eq
  cover := cover
  memPt := memPt
  memPt_eq := memPt_eq
  -- **constructed**: the sample point *is* the trajectory, so the reading is the
  -- identity, its law is `trajLaw θ` on the nose, and the oracles are `trajOracles`.
  toTraj := id
  toTraj_meas := measurable_id.aemeasurable
  law_eq := Measure.map_id
  oracle_eq := fun _ => rfl
  cover_eq := cover_eq
  volAlg := volAlg
  volCoins := volCoins
  volED_eq := volED_eq
  volCoins_good := volCoins_good
  vol_pos := vol_pos
  big := big

/-! ## The constructed fields, read back

`mΩ`, `isProb`, `M_eq`, `toTraj_meas`, `law_eq` and `oracle_eq` are instance- or
`Prop`-valued: that they are discharged is exactly the statement that
`Ttc.canonicalTtcProb` elaborates, and there is nothing further to say about their
*values*.  The four fields below carry data, so each gets a lemma. -/

variable (ε δ : ℝ) (hε0 : 0 < ε) (hε1 : ε ≤ 1) (hδ0 : 0 < δ) (hδ1 : δ ≤ 1)
  (atoms : A → LinAtom n) (φ : BForm A) (toDNF : BForm A → DNF A)
  (isDNF : IsDNFOf (toDNF φ) φ) (isPositive : DNF.IsPositive (toDNF φ))
  (P : Params) (eps_eq : P.ε = ε) (delta_eq : P.δ = δ) (dim_eq : P.n = n)
  (cubes_le : (Nat.card {c : Cube A // c ∈ toDNF φ} : ℝ) ≤ P.m)
  (facets_le : (Nat.card (FacetIndex (toDNF φ)) : ℝ) ≤ P.r)
  (normal_ne_zero : ∀ j : FacetIndex (toDNF φ), 0 < ∑ k, (atoms j.2.val.atom).coeff k ^ 2)
  (cen : {c : Cube A // c ∈ toDNF φ} → Space n) (gammaHat : ℝ) (hgammaHat : 0 < gammaHat)
  (ball_subset : ∀ i, Metric.ball (cen i) gammaHat ⊆
    region (fun a => (atoms a).halfspace) i.val)
  (volume_ne_top : ∀ i : {c : Cube A // c ∈ toDNF φ},
    volume (region (fun a => (atoms a).halfspace) i.val) ≠ ⊤)
  (ρ : ℤ) (rho_eq : ρ = P.precision gammaHat)
  (L : ℝ) (L_eq : L = normalisedCount (fun a => (atoms a).halfspace) φ ρ)
  (Lidx : ℕ) (ptE : Fin Lidx → Space n) (ptE_inj : Function.Injective ptE)
  (ptE_mem : ∀ s, ptE s ∈
    sol (fun a => (atoms a).halfspace) φ ∩ fineLattice n (latticeScale ρ))
  (ptE_onto : ∀ x ∈ sol (fun a => (atoms a).halfspace) φ ∩ fineLattice n (latticeScale ρ),
    ∃ s, ptE s = x)
  (θ : Fin Lidx → ℝ) (vol : Cube A → ℝ) (sampD : Cube A → Space n → ℝ)
  (sampler : KV97Sampler A n (fun a => (atoms a).halfspace) (toDNF φ) ρ P.epsPrime sampD)
  (theta_eq : ∀ s, ∃ i, i ∈ toDNF φ ∧ ptE s ∈ region (fun a => (atoms a).halfspace) i ∧
    θ s = sampD i (ptE s) * vol i)
  (cover : Space n → Cube A → Bool) (memPt : Cube A → Fin Lidx → Bool)
  (memPt_eq : ∀ i ∈ toDNF φ, ∀ s,
    memPt i s = true ↔ ptE s ∈ region (fun a => (atoms a).halfspace) i)
  (cover_eq : ∀ s i, cover (ptE s) i = memPt i s)
  (gen_mem : ∀ (t : ℕ → Fin Lidx → ℕ) (i : Cube A) (j N : ℕ), i ∈ toDNF φ →
    ∀ s ∈ (trajOracles ptE_inj vol cover memPt t).gen i j N ρ,
      s ∈ region (fun a => (atoms a).halfspace) i ∩ fineLattice n (latticeScale ρ))
  (volAlg : VolumeAlgorithm n) (volCoins : volAlg.Ω)
  (volED_eq : ∀ (i : Cube A) (hi : i ∈ toDNF φ), vol i =
    gammaHat ^ n * volAlg.est
      (roundBody (cen ⟨i, hi⟩) gammaHat (region (fun a => (atoms a).halfspace) i))
      P.epsPrime P.deltaPrime volCoins)
  (volCoins_good : ∀ i ∈ toDNF φ, vol i ∈
    relErr P.epsPrime (volume (region (fun a => (atoms a).halfspace) i)).toReal)
  (vol_pos : ∀ i ∈ toDNF φ, 0 < vol i)
  (big : (1 - P.epsPrime) * P.thresh / 8 ≤ ∑ s, θ s)

/-- **The sample space is the trajectory space** of the coupled level family — a
construction, not a field. -/
theorem canonicalTtcProb_Omega :
    (canonicalTtcProb ε δ hε0 hε1 hδ0 hδ1 atoms φ toDNF isDNF isPositive P eps_eq delta_eq
      dim_eq cubes_le facets_le normal_ne_zero cen gammaHat hgammaHat ball_subset volume_ne_top
      ρ rho_eq L L_eq Lidx ptE ptE_inj ptE_mem ptE_onto θ vol sampD sampler theta_eq cover
      memPt memPt_eq cover_eq gen_mem volAlg volCoins volED_eq volCoins_good vol_pos big).Ω
      = (ℕ → Fin Lidx → ℕ) := rfl

/-- **The law is `Ttc.trajLaw`** at the instance's own rates. -/
theorem canonicalTtcProb_mu :
    (canonicalTtcProb ε δ hε0 hε1 hδ0 hδ1 atoms φ toDNF isDNF isPositive P eps_eq delta_eq
      dim_eq cubes_le facets_le normal_ne_zero cen gammaHat hgammaHat ball_subset volume_ne_top
      ρ rho_eq L L_eq Lidx ptE ptE_inj ptE_mem ptE_onto θ vol sampD sampler theta_eq cover
      memPt memPt_eq cover_eq gen_mem volAlg volCoins volED_eq volCoins_good vol_pos big).μ
      = trajLaw θ := rfl

/-- **The oracle bundle is `Ttc.trajOracles`** — the run reads the family. -/
theorem canonicalTtcProb_O :
    (canonicalTtcProb ε δ hε0 hε1 hδ0 hδ1 atoms φ toDNF isDNF isPositive P eps_eq delta_eq
      dim_eq cubes_le facets_le normal_ne_zero cen gammaHat hgammaHat ball_subset volume_ne_top
      ρ rho_eq L L_eq Lidx ptE ptE_inj ptE_mem ptE_onto θ vol sampD sampler theta_eq cover
      memPt memPt_eq cover_eq gen_mem volAlg volCoins volED_eq volCoins_good vol_pos big).O
      = fun t => trajOracles ptE_inj vol cover memPt t := rfl

/-- **The reading is the identity** — there is no coupling left to assume. -/
theorem canonicalTtcProb_toTraj :
    (canonicalTtcProb ε δ hε0 hε1 hδ0 hδ1 atoms φ toDNF isDNF isPositive P eps_eq delta_eq
      dim_eq cubes_le facets_le normal_ne_zero cen gammaHat hgammaHat ball_subset volume_ne_top
      ρ rho_eq L L_eq Lidx ptE ptE_inj ptE_mem ptE_onto θ vol sampD sampler theta_eq cover
      memPt memPt_eq cover_eq gen_mem volAlg volCoins volED_eq volCoins_good vol_pos big).toTraj
      = id := rfl

/-- **The interpretation of the atoms is constructed** — `M` is not a free field
beside `atoms`, and `M_eq` is not an assumption. -/
theorem canonicalTtcProb_M :
    (canonicalTtcProb ε δ hε0 hε1 hδ0 hδ1 atoms φ toDNF isDNF isPositive P eps_eq delta_eq
      dim_eq cubes_le facets_le normal_ne_zero cen gammaHat hgammaHat ball_subset volume_ne_top
      ρ rho_eq L L_eq Lidx ptE ptE_inj ptE_mem ptE_onto θ vol sampD sampler theta_eq cover
      memPt memPt_eq cover_eq gen_mem volAlg volCoins volED_eq volCoins_good vol_pos big).M
      = fun a => (atoms a).halfspace := rfl

end Canonical

/-! ## The faithfulness check: the box witness goes through the constructor

`Ttc.Box.boxProb` (`Ttc/Witness/BoxProb.lean`) is the development's only witness
for `Ttc.TtcProb`, and the one thing that keeps `Ttc.TtcProb.volume_estimate` from
being vacuous.  If it could not be built by `Ttc.canonicalTtcProb`, then one of the
ten canonical choices above would be an assumption disguised as a construction.

It can, and *definitionally*: the equation below is `rfl`.  Concretely, this
checks that the box's

* `Ω` really is `ℕ → Fin (Ttc.Box.Lidx n hn) → ℕ`,
* `μ` really is `Ttc.trajLaw (Ttc.Box.th n hn)`,
* `O` really is `Ttc.trajOracles` at the box's data (`Ttc.Box.orc` unfolds to it),
* `toTraj` really is the identity, and
* `M` really is `fun a => (Ttc.Box.atm n hn a).halfspace`,

with the six `Prop`/instance-valued canonical fields matching by proof irrelevance
and instance resolution.  `Witness/BoxProb.lean` is unchanged.

The 48 supplied arguments are passed as the box's own field values, so nothing
about them is being checked here — that is the point.  What *is* checked is that
the ten canonical fields, which are **not** arguments and so cannot be supplied,
come out right.  (Manual negative control, not part of the build: replacing
`Ttc.Box.th n hn` by `fun _ => 0` in `Ttc.Box.boxProb_mu`, or `Ttc.Box.vl n hn` by
`fun _ => 0` in `Ttc.Box.boxProb_O`, makes `rfl` fail — so these are not
`rfl`-by-triviality.) -/

namespace Box

variable {n : ℕ}

/-- **The witness goes through the smart constructor.**  `Ttc.Box.boxProb` is
`Ttc.canonicalTtcProb` applied to the box's own data — the geometry, the parameter
block `Ttc.Box.par`, the Kannan–Vempala sampler, and the exact volume oracle.  The
probability space, its measure, the oracle bundle and the four linking fields are
*not* supplied: they are the canonical ones. -/
theorem boxProb_eq_canonical (n : ℕ) (hn : 1 ≤ n) :
    boxProb n hn =
      canonicalTtcProb (A := Fin n ⊕ Fin n) (n := n)
        1 1 one_pos le_rfl one_pos le_rfl
        (atm n hn) (boxForm n hn) Ttc.toDNF
        (boxProb n hn).isDNF (boxProb n hn).isPositive
        (par n hn) rfl rfl rfl
        (boxProb n hn).cubes_le (boxProb n hn).facets_le (boxProb n hn).normal_ne_zero
        (fun _ => boxCentre n (side n hn)) (gam n hn) (gam_pos hn)
        (boxProb n hn).ball_subset (boxProb n hn).volume_ne_top
        (rho n hn) rfl
        (Lval n hn) rfl
        (Box.Lidx n hn) (pt n hn) (pt_injective hn)
        (boxProb n hn).ptE_mem (boxProb n hn).ptE_onto
        (th n hn) (vl n hn) (smp n hn) (boxProb n hn).sampler (boxProb n hn).theta_eq
        (cov n) (mm n hn) (boxProb n hn).memPt_eq (cov_eq hn)
        (boxProb n hn).gen_mem
        (VolumeAlgorithm.exact n) () (boxProb n hn).volED_eq (boxProb n hn).volCoins_good
        (boxProb n hn).vol_pos (boxProb n hn).big := rfl

/-! ### The five data identifications, spelled out

`Ttc.Box.boxProb_eq_canonical` already contains these, but stating them separately
is what makes the fit auditable without reading the 48-argument application. -/

/-- The box's sample space **is** the trajectory space. -/
theorem boxProb_Omega (n : ℕ) (hn : 1 ≤ n) :
    (boxProb n hn).Ω = (ℕ → Fin (Box.Lidx n hn) → ℕ) := rfl

/-- The box's law **is** `Ttc.trajLaw` at its own rates. -/
theorem boxProb_mu (n : ℕ) (hn : 1 ≤ n) : (boxProb n hn).μ = trajLaw (th n hn) := rfl

/-- The box's oracle bundle **is** `Ttc.trajOracles`. -/
theorem boxProb_O (n : ℕ) (hn : 1 ≤ n) :
    (boxProb n hn).O = fun t => trajOracles (pt_injective hn) (vl n hn) (cov n) (mm n hn) t :=
  rfl

/-- The box reads its sample point **by the identity**. -/
theorem boxProb_toTraj (n : ℕ) (hn : 1 ≤ n) : (boxProb n hn).toTraj = id := rfl

/-- The box's interpretation of atoms **is** the one they denote. -/
theorem boxProb_M (n : ℕ) (hn : 1 ≤ n) :
    (boxProb n hn).M = fun a => (atm n hn a).halfspace := rfl

end Box

/-! ## Axiom profile

Every declaration of this file, checked transitively (`CLAUDE.md` §4). Expect
`[propext, Classical.choice, Quot.sound]` throughout. -/

#print axioms canonicalTtcProb
#print axioms canonicalTtcProb_Omega
#print axioms canonicalTtcProb_mu
#print axioms canonicalTtcProb_O
#print axioms canonicalTtcProb_toTraj
#print axioms canonicalTtcProb_M
#print axioms Box.boxProb_eq_canonical
#print axioms Box.boxProb_Omega
#print axioms Box.boxProb_mu
#print axioms Box.boxProb_O
#print axioms Box.boxProb_toTraj
#print axioms Box.boxProb_M

end Ttc

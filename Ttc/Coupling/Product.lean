/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import Ttc.Exec.Canonical
import Ttc.Model.Theorem
import Ttc.Volume.Bridge

/-!
# `Coupling/Product`: the headline over the **joint** randomness

README finding 13a. `Ttc.TtcProb.volume_estimate` reads

```lean
1 - T.δ ≤ (T.μ {ω | ttcOutput … ω ∈ relErr T.ε (volSol T.M T.φ)}).toReal
```

and `T.μ` is the *run's* randomness alone. The volume oracle's randomness is the
field `volCoins : T.volAlg.Ω`, a **fixed** value pinned by `volCoins_good`. So the
headline says: *at one good draw of the volume oracle's coins, the run succeeds
with probability `1 − δ`.* The paper's claim is over the **joint** randomness of
run and oracle, at `1 − δ − δ/4`.

This file states and proves that joint form, additively: nothing in
`Coupling/{Family,Run,Transfer}`, `Model/ProblemSetting`, `Model/Theorem` or
`Witness/BoxProb` is touched, and `Ttc.TtcProb.volume_estimate` keeps its exact
statement and axiom profile.

## What the joint space actually is — and what it is **not**

It is **not** `T.μ.prod T.volAlg.μ`. The run's law `Ttc.trajLaw θ` is determined by
the rates `θ`, `theta_eq` ties `θ s` to `vol i`, and `volED_eq` ties `vol i` to the
oracle's estimate at the coins — so the run's law is a *function of the coins*.
The two sources of randomness are physically independent, but their joint
distribution on `volAlg.Ω × (ℕ → Fin Lidx → ℕ)` is still **not** a product of two
fixed marginals, because the second marginal moves with the first coordinate. A
product measure is therefore the wrong object; the right one is the
composition-product

```
volAlg.μ ⊗ₘ κ ,  κ c = trajLaw (θ c)
```

on `volAlg.Ω × (ℕ → Fin Lidx → ℕ)` — coins first, then the run they drive. Its
value on a set is the iterated integral `∫⁻ c, trajLaw (θ c) (slice) ∂volAlg.μ`,
and that iterated integral is what `Ttc.volume_estimate_joint` bounds, with no
kernel needed. `Ttc.volume_estimate_joint_compProd` upgrades it to a statement
about a single sample point of a single space, at the cost of one hypothesis: that
`c ↦ trajLaw (θ c)` *is* a Markov kernel, i.e. is measurable in `c`. That is a
regularity assumption on the map, not a probabilistic one; it is discharged for the
exact oracle by `Ttc.kernelOfDiscrete`.

## The three steps

1. `Ttc.TtcProb.volume_estimate_traj` — the existing conclusion, transported from
   the abstract space `T.Ω` onto the **constructed** trajectory space
   `ℕ → Fin T.Lidx → ℕ`. This is where `law_eq`/`oracle_eq` are spent, via
   `MeasureTheory.Measure.le_map_apply`; note the direction is favourable, so no
   measurability of the good set is needed (and none is available — the existing
   proof reaches its set by `measure_mono` from the `numlattice` event).
2. `Ttc.toReal_lintegral_ge_of_cond` — the abstract union bound: an event of
   measure `≥ 1 − b` on which a conditional probability is `≥ a` gives
   `≥ a − b` for the average. Nothing project-specific.
3. `Ttc.volume_estimate_joint` — step 2 applied to step 1, with the conditional
   guarantee at each good coin supplied by `Ttc.canonicalTtcProb`
   (`Ttc/Exec/Canonical.lean`): every good coin gives a genuine `Ttc.TtcProb`
   whose space *is* the trajectory space, so `volume_estimate` applies there.

**Nothing here assumes the conclusion.** The good event `G` enters as a set with a
measure bound and a spelled-out meaning (`hGgood`); `Ttc.measurableSet_volGood`,
`Ttc.measure_volGood_ge_of_length` and `Ttc.mem_relErr_of_mem_volGood` discharge
the three at `G = Ttc.volGood …`, i.e. from Cousins–Vempala Theorem 1.1 and the
union bound over the `m` calls.

## Vacuity guard

`δ + δ/4 ≥ 1` makes the conclusion empty. `Ttc.TtcProb`'s `hδ0`/`hδ1` give only
`0 < δ ≤ 1`, so `δ ≤ 4/5` is **not** available and is *not* assumed here: the
theorems below hold for every `δ ∈ (0,1]` and are simply uninformative above `4/5`.
That is stated rather than patched.
-/

namespace Ttc

open MeasureTheory ProbabilityTheory Set

/-! ## Step 2, in the abstract

Two measure-theoretic lemmas with no `Ttc` content. Both are stated for arbitrary
sets — in particular neither needs the "success" set to be measurable, which
matters because the development never proves that the run's good set is.
-/

section Abstract

variable {C Ω : Type*} [MeasurableSpace C] [MeasurableSpace Ω]

/-- **The union bound behind `1 − δ − δ/4`.**

If `G` carries mass `≥ 1 − b` and, at every point of `G`, the conditional law
`μ c` gives the (arbitrary, possibly non-measurable) set `S c` mass `≥ a`, then
the average `∫⁻ c, μ c (S c) ∂ν` is at least `a − b`.

The proof does not go through `a·(ν G)` and then subtract: it bounds the
integrand below by `a` on `G` and by `0` off it, which is exactly the two failure
events being union-bounded. -/
theorem toReal_lintegral_ge_of_cond (ν : Measure C) [IsProbabilityMeasure ν]
    (μ : C → Measure Ω) (hμ : ∀ c, IsProbabilityMeasure (μ c))
    (S : C → Set Ω) (G : Set C) (hG : MeasurableSet G) {a b : ℝ}
    (ha0 : 0 ≤ a) (ha1 : a ≤ 1) (hb0 : 0 ≤ b)
    (hGb : 1 - b ≤ (ν G).toReal)
    (hcond : ∀ c ∈ G, a ≤ (μ c (S c)).toReal) :
    a - b ≤ (∫⁻ c, μ c (S c) ∂ν).toReal := by
  -- the average is a probability, hence finite
  have hle_one : (∫⁻ c, μ c (S c) ∂ν) ≤ 1 := by
    calc (∫⁻ c, μ c (S c) ∂ν) ≤ ∫⁻ _c, 1 ∂ν :=
          lintegral_mono fun c => by haveI := hμ c; exact prob_le_one
      _ = 1 := by simp
  have hne : (∫⁻ c, μ c (S c) ∂ν) ≠ ⊤ := ne_top_of_le_ne_top ENNReal.one_ne_top hle_one
  -- pointwise lower bound by the indicator of `G` at height `a`
  have hind : ∀ c, G.indicator (fun _ => ENNReal.ofReal a) c ≤ μ c (S c) := by
    intro c
    by_cases hc : c ∈ G
    · rw [Set.indicator_of_mem hc]
      exact ENNReal.ofReal_le_of_le_toReal (hcond c hc)
    · rw [Set.indicator_of_notMem hc]
      exact zero_le
  have hlow : ENNReal.ofReal a * ν G ≤ ∫⁻ c, μ c (S c) ∂ν := by
    calc ENNReal.ofReal a * ν G
        = ∫⁻ c, G.indicator (fun _ => ENNReal.ofReal a) c ∂ν := by
          rw [lintegral_indicator hG, setLIntegral_const]
      _ ≤ _ := lintegral_mono hind
  -- transfer to reals
  have hlowR : a * (ν G).toReal ≤ (∫⁻ c, μ c (S c) ∂ν).toReal := by
    have := ENNReal.toReal_mono hne hlow
    rwa [ENNReal.toReal_mul, ENNReal.toReal_ofReal ha0] at this
  nlinarith [hlowR, mul_le_mul_of_nonneg_left hGb ha0]

/-- **The iterated integral is a lower bound for the composition-product**, for an
*arbitrary* set. `MeasureTheory.Measure.compProd_apply` needs the set measurable;
this one does not, because a measure is the outer measure of its measurable hull.
Same proof as Mathlib's `ProbabilityTheory.le_compProd_apply` for kernels. -/
theorem le_compProd_apply_of_forall (ν : Measure C) [SFinite ν] (κ : Kernel C Ω)
    [IsSFiniteKernel κ] (S : Set (C × Ω)) :
    ∫⁻ c, κ c (Prod.mk c ⁻¹' S) ∂ν ≤ (ν ⊗ₘ κ) S := by
  calc ∫⁻ c, κ c (Prod.mk c ⁻¹' S) ∂ν
      ≤ ∫⁻ c, κ c (Prod.mk c ⁻¹' toMeasurable (ν ⊗ₘ κ) S) ∂ν :=
        lintegral_mono fun _ => measure_mono (Set.preimage_mono (subset_toMeasurable _ _))
    _ = (ν ⊗ₘ κ) (toMeasurable (ν ⊗ₘ κ) S) :=
        (Measure.compProd_apply (measurableSet_toMeasurable _ _)).symm
    _ = (ν ⊗ₘ κ) S := measure_toMeasurable S

/-- **From the iterated integral to the joint measure.** The bridge between the
kernel-free statement `Ttc.volume_estimate_joint` and the single-sample-point
statement `Ttc.volume_estimate_joint_compProd`. `S` is arbitrary. -/
theorem toReal_compProd_ge_of_lintegral_ge (ν : Measure C) [IsProbabilityMeasure ν]
    (κ : Kernel C Ω) [IsMarkovKernel κ] (S : Set (C × Ω)) {r : ℝ}
    (h : r ≤ (∫⁻ c, κ c (Prod.mk c ⁻¹' S) ∂ν).toReal) :
    r ≤ ((ν ⊗ₘ κ) S).toReal :=
  le_trans h (ENNReal.toReal_mono (measure_ne_top _ _) (le_compProd_apply_of_forall ν κ S))

/-- **When the coin space is discrete, the kernel of step 3 always exists.** This
is the non-vacuity check for `Ttc.volume_estimate_joint_compProd`'s kernel
hypothesis: for the exact volume oracle `Ttc.VolumeAlgorithm.exact`, whose coin
space is `Unit`, the hypothesis is free. -/
noncomputable def kernelOfDiscrete [DiscreteMeasurableSpace C] (f : C → Measure Ω) :
    Kernel C Ω :=
  ⟨f, Measurable.of_discrete⟩

@[simp] theorem kernelOfDiscrete_apply [DiscreteMeasurableSpace C] (f : C → Measure Ω) (c : C) :
    kernelOfDiscrete f c = f c := rfl

end Abstract

/-! ## Step 1: the guarantee on the constructed trajectory space -/

namespace TtcProb

variable {A : Type*} {n : ℕ} (T : TtcProb A n)

/-- **`thm:volumettc`, moved onto the trajectory space.**

`Ttc.TtcProb.volume_estimate` is about the abstract field `T.μ` on the abstract
field `T.Ω`. Here the same bound is stated about `Ttc.trajLaw T.θ` on
`ℕ → Fin T.Lidx → ℕ` — the space `Ttc.canonicalTtcProb` *constructs*, and the only
space in which coins from different draws can be compared.

`law_eq` and `oracle_eq` are what pay for the move, and the inequality direction is
the favourable one: `MeasureTheory.Measure.le_map_apply` gives
`T.μ (toTraj ⁻¹' B) ≤ (map toTraj T.μ) B` for **every** `B`, so no measurability of
the good set is required — and none is available, since `volume_estimate` reaches
its set by `measure_mono` from the `numlattice` event rather than by computing it. -/
theorem volume_estimate_traj :
    1 - T.δ ≤ (trajLaw T.θ
      {t | ttcOutput T.P (fun t => trajOracles T.ptE_inj T.vol T.cover T.memPt t)
             T.toDNF T.ρ T.φ t ∈ relErr T.ε (volSol T.M T.φ)}).toReal := by
  letI := T.mΩ
  haveI := T.isProb
  set B : Set (ℕ → Fin T.Lidx → ℕ) :=
    {t | ttcOutput T.P (fun t => trajOracles T.ptE_inj T.vol T.cover T.memPt t)
           T.toDNF T.ρ T.φ t ∈ relErr T.ε (volSol T.M T.φ)} with hB
  have hpre : {ω | ttcOutput T.P T.O T.toDNF T.ρ T.φ ω ∈ relErr T.ε (volSol T.M T.φ)}
      = T.toTraj ⁻¹' B := by
    ext ω
    simp only [hB, Set.mem_setOf_eq, Set.mem_preimage, ttcOutput, T.oracle_eq ω]
  have h1 := T.volume_estimate
  rw [hpre] at h1
  refine le_trans h1 (ENNReal.toReal_mono (measure_ne_top _ _) ?_)
  calc T.μ (T.toTraj ⁻¹' B) ≤ (T.μ.map T.toTraj) B := Measure.le_map_apply T.toTraj_meas B
    _ = trajLaw T.θ B := by rw [T.law_eq]

end TtcProb

/-! ## The volume oracle's good event, as the `G` of step 3

Three lemmas producing exactly the three hypotheses `Ttc.volume_estimate_joint`
asks of its good event, from `Ttc.measure_volGood_ge` — i.e. from Cousins–Vempala
Theorem 1.1 and the union bound over the `m` calls, nothing new.
-/

/-- **The good event of the `m` `Vol_ED` calls is measurable.** A finite
intersection of the single-call good events, each measurable by
`Ttc.VolumeAlgorithm.measurableSet_good` (which is where the interface's
`est_meas` is spent). -/
theorem measurableSet_volGood {n m : ℕ} (V : VolumeAlgorithm n) (γ ε' δ' : ℝ)
    (cen : Fin m → Space n) (K : Fin m → Set (Space n)) :
    MeasurableSet[V.mΩ] (volGood V γ ε' δ' cen K) := by
  letI := V.mΩ
  have hrw : volGood V γ ε' δ' cen K = ⋂ j, {ω | γ ^ n * V.est (roundBody (cen j) γ (K j)) ε' δ' ω
      ∈ relErr ε' (volume (K j)).toReal} := by
    ext ω; simp [volGood]
  rw [hrw]
  exact MeasurableSet.iInter fun j => V.measurableSet_good (cen j) γ ε' δ' (K j)

/-- **The good event says exactly what `volCoins_good` says.** Membership in
`Ttc.volGood`, indexed by loop position, unpacks to the two-sided estimate at
every cube of the DNF — which is the form `Ttc.canonicalTtcProb` consumes. This is
`Ttc.TtcProb.volCoins_mem_volEvent` read in the other direction, and for an
arbitrary coin rather than the structure's fixed one. -/
theorem mem_relErr_of_mem_volGood {A : Type*} {n : ℕ} (V : VolumeAlgorithm n)
    (M : A → Set (Space n)) (D : DNF A) (γ ε' δ' : ℝ)
    (cen : {c : Cube A // c ∈ D} → Space n) (vol : V.Ω → Cube A → ℝ)
    (volED_eq : ∀ (c : V.Ω) (i : Cube A) (hi : i ∈ D), vol c i =
      γ ^ n * V.est (roundBody (cen ⟨i, hi⟩) γ (region M i)) ε' δ' c)
    {c : V.Ω}
    (hc : c ∈ volGood V γ ε' δ' (fun j : Fin D.length => cen ⟨D.get j, List.get_mem _ _⟩)
            (fun j : Fin D.length => region M (D.get j))) :
    ∀ i ∈ D, vol c i ∈ relErr ε' (volume (region M i)).toReal := by
  intro i hi
  obtain ⟨j, hj⟩ := List.mem_iff_get.mp hi
  rw [volED_eq c i hi]
  subst hj
  exact hc j

/-- **The volume oracle fails with probability at most `δ/4`.**

`Ttc.measure_volGood_ge` bounds the failure of the `m` calls by `m·δ'`, and
`δ' = δ/(4m)` (`Ttc.Params.deltaPrime`) turns that into `δ/4` — the share
`Ttc.Params.vol_failure_eq` reserves. Stated for a bare `Ttc.Params` and a bare
list of cubes rather than for a `Ttc.TtcProb`, because at this point the coins are
still ranging: there is no `Ttc.TtcProb` to speak of until a *good* coin is
chosen. -/
theorem measure_volGood_ge_of_length {A : Type*} {n : ℕ} (V : VolumeAlgorithm n)
    (M : A → Set (Space n)) (D : DNF A) (P : Params) {δ γ : ℝ}
    (delta_eq : P.δ = δ) (hδ0 : 0 < δ) (hδ1 : δ ≤ 1) (hγ : 0 < γ)
    (cen : {c : Cube A // c ∈ D} → Space n)
    (hball : ∀ i : {c : Cube A // c ∈ D}, Metric.ball (cen i) γ ⊆ region M i.val)
    (hconv : ∀ i : {c : Cube A // c ∈ D}, Convex ℝ (region M i.val))
    (hfin : ∀ i : {c : Cube A // c ∈ D}, volume (region M i.val) ≠ ⊤)
    (hm : (D.length : ℝ) ≤ P.m) :
    1 - δ / 4 ≤ (V.μ (volGood V γ P.epsPrime P.deltaPrime
      (fun j : Fin D.length => cen ⟨D.get j, List.get_mem _ _⟩)
      (fun j : Fin D.length => region M (D.get j)))).toReal := by
  have hmP : (1:ℝ) ≤ (P.m : ℝ) := by exact_mod_cast P.hm
  have hε : 0 < P.epsPrime := by have := P.hε0; unfold Params.epsPrime; linarith
  have hδP : 0 < P.δ := by rw [delta_eq]; exact hδ0
  have hd0 : 0 < P.deltaPrime := by unfold Params.deltaPrime; positivity
  have hd1 : P.deltaPrime < 1 := by
    have hδ1P : P.δ ≤ 1 := by rw [delta_eq]; exact hδ1
    unfold Params.deltaPrime
    rw [div_lt_one (by linarith)]
    linarith
  have hbase := measure_volGood_ge (m := D.length) V (γ := γ) (ε' := P.epsPrime)
    (δ' := P.deltaPrime) (cen := fun j : Fin D.length => cen ⟨D.get j, List.get_mem _ _⟩)
    (K := fun j : Fin D.length => region M (D.get j)) hγ hε hd0 hd1
    (fun j => hball ⟨D.get j, List.get_mem _ _⟩) (fun j => hconv ⟨D.get j, List.get_mem _ _⟩)
    (fun j => hfin ⟨D.get j, List.get_mem _ _⟩)
  have hstep : (D.length : ℝ) * P.deltaPrime ≤ (P.m : ℝ) * P.deltaPrime :=
    mul_le_mul_of_nonneg_right hm hd0.le
  rw [P.vol_failure_eq, delta_eq] at hstep
  linarith

/-! ## Step 3: the headline over the joint randomness -/

section Joint

variable {A : Type*} {n : ℕ}

/-- **README finding 13a, closed: `thm:volumettc` over the joint randomness of the
run *and* the volume oracle.**

The conclusion is the iterated integral

```
∫⁻ c, trajLaw (θ c) {t | ttcOutput … ∈ relErr ε (volSol M φ)} ∂volAlg.μ
```

— the coins are drawn from `volAlg.μ`, and *for each coin* the run is drawn from
the law its own volume estimates induce. That dependence is the reason the object
is a composition-product and not a product: `θ c` genuinely varies with `c`.

Everything except `θ`, `vol` and the good event is coin-free and is passed
verbatim to `Ttc.canonicalTtcProb`, whose ten constructed fields supply the
probability space — so the space this statement integrates over is *built*, not
assumed.

**The good event `G` is a parameter with a spelled-out meaning.** `hGprob` is its
mass and `hGgood` is what it says; both are discharged from Cousins–Vempala
Theorem 1.1 by `Ttc.measure_volGood_ge_of_length` and
`Ttc.mem_relErr_of_mem_volGood`, at `G = Ttc.volGood …`. No hypothesis here
asserts the conclusion: `hGgood` is `Vol_ED`'s accuracy at a *good* coin, exactly
the `volCoins_good` field that `Ttc.TtcProb` already carries, and the theorem's
work is to average it against the coins.

**Vacuity.** `hδ1 : δ ≤ 1` is all that is assumed, so at `δ > 4/5` the bound
`1 − δ − δ/4` is below `0` and says nothing. That is the honest content of the
paper's own budget; no extra hypothesis is inserted to hide it. -/
theorem volume_estimate_joint
    (ε δ : ℝ) (hε0 : 0 < ε) (hε1 : ε ≤ 1) (hδ0 : 0 < δ) (hδ1 : δ ≤ 1)
    (atoms : A → LinAtom n) (M : A → Set (Space n)) (M_eq : M = fun a => (atoms a).halfspace)
    (φ : BForm A) (toDNF : BForm A → DNF A)
    (isDNF : IsDNFOf (toDNF φ) φ) (isPositive : DNF.IsPositive (toDNF φ))
    (P : Params) (eps_eq : P.ε = ε) (delta_eq : P.δ = δ) (dim_eq : P.n = n)
    (cubes_le : (Nat.card {c : Cube A // c ∈ toDNF φ} : ℝ) ≤ P.m)
    (facets_le : (Nat.card (FacetIndex (toDNF φ)) : ℝ) ≤ P.r)
    (normal_ne_zero : ∀ j : FacetIndex (toDNF φ), 0 < ∑ k, (atoms j.2.val.atom).coeff k ^ 2)
    (cen : {c : Cube A // c ∈ toDNF φ} → Space n) (gammaHat : ℝ) (hgammaHat : 0 < gammaHat)
    (ball_subset : ∀ i, Metric.ball (cen i) gammaHat ⊆ region M i.val)
    (volume_ne_top : ∀ i : {c : Cube A // c ∈ toDNF φ}, volume (region M i.val) ≠ ⊤)
    (ρ : ℤ) (rho_eq : ρ = P.precision gammaHat)
    (L : ℝ) (L_eq : L = normalisedCount M φ ρ)
    (Lidx : ℕ) (ptE : Fin Lidx → Space n) (ptE_inj : Function.Injective ptE)
    (ptE_mem : ∀ s, ptE s ∈ sol M φ ∩ fineLattice n (latticeScale ρ))
    (ptE_onto : ∀ x ∈ sol M φ ∩ fineLattice n (latticeScale ρ), ∃ s, ptE s = x)
    (volAlg : VolumeAlgorithm n)
    (θ : volAlg.Ω → Fin Lidx → ℝ) (vol : volAlg.Ω → Cube A → ℝ)
    (sampD : Cube A → Space n → ℝ)
    (sampler : KV97Sampler A n M (toDNF φ) ρ P.epsPrime sampD)
    (theta_eq : ∀ (c : volAlg.Ω) (s : Fin Lidx), ∃ i, i ∈ toDNF φ ∧ ptE s ∈ region M i ∧
      θ c s = sampD i (ptE s) * vol c i)
    (cover : Space n → Cube A → Bool) (memPt : Cube A → Fin Lidx → Bool)
    (memPt_eq : ∀ i ∈ toDNF φ, ∀ s, memPt i s = true ↔ ptE s ∈ region M i)
    (cover_eq : ∀ s i, cover (ptE s) i = memPt i s)
    (gen_mem : ∀ (c : volAlg.Ω) (t : ℕ → Fin Lidx → ℕ) (i : Cube A) (j N : ℕ), i ∈ toDNF φ →
      ∀ s ∈ (trajOracles ptE_inj (vol c) cover memPt t).gen i j N ρ,
        s ∈ region M i ∩ fineLattice n (latticeScale ρ))
    (volED_eq : ∀ (c : volAlg.Ω) (i : Cube A) (hi : i ∈ toDNF φ), vol c i =
      gammaHat ^ n * volAlg.est (roundBody (cen ⟨i, hi⟩) gammaHat (region M i))
        P.epsPrime P.deltaPrime c)
    (G : Set volAlg.Ω) (hGmeas : MeasurableSet[volAlg.mΩ] G)
    (hGprob : 1 - δ / 4 ≤ (volAlg.μ G).toReal)
    (hGgood : ∀ c ∈ G, ∀ i ∈ toDNF φ, vol c i ∈ relErr P.epsPrime (volume (region M i)).toReal)
    (vol_pos : ∀ c ∈ G, ∀ i ∈ toDNF φ, 0 < vol c i)
    (big : ∀ c ∈ G, (1 - P.epsPrime) * P.thresh / 8 ≤ ∑ s, θ c s) :
    1 - δ - δ / 4 ≤
      (∫⁻ c, trajLaw (θ c)
          {t | ttcOutput P (fun t => trajOracles ptE_inj (vol c) cover memPt t) toDNF ρ φ t
            ∈ relErr ε (volSol M φ)} ∂volAlg.μ).toReal := by
  letI := volAlg.mΩ
  haveI := volAlg.isProb
  subst M_eq
  refine toReal_lintegral_ge_of_cond volAlg.μ (fun c => trajLaw (θ c))
    (fun c => isProbabilityMeasure_trajLaw (θ c))
    (fun c => {t | ttcOutput P (fun t => trajOracles ptE_inj (vol c) cover memPt t) toDNF ρ φ t
      ∈ relErr ε (volSol (fun a => (atoms a).halfspace) φ)})
    G hGmeas (by linarith) (by linarith) (by linarith) hGprob ?_
  intro c hc
  exact (canonicalTtcProb ε δ hε0 hε1 hδ0 hδ1 atoms φ toDNF isDNF isPositive P eps_eq
    delta_eq dim_eq cubes_le facets_le normal_ne_zero cen gammaHat hgammaHat ball_subset
    volume_ne_top ρ rho_eq L L_eq Lidx ptE ptE_inj ptE_mem ptE_onto (θ c) (vol c) sampD sampler
    (theta_eq c) cover memPt memPt_eq cover_eq (gen_mem c) volAlg c (volED_eq c) (hGgood c hc)
    (vol_pos c hc) (big c hc)).volume_estimate_traj

/-- **The same bound as a statement about one sample point of one space.**

`Ttc.volume_estimate_joint` is an iterated integral; the nfalean template
(`ApproxNFA.approxNFA_countNFA`) states accuracy over a single `ω` of a single
constructed space. The composition-product `volAlg.μ ⊗ₘ κ` on
`volAlg.Ω × (ℕ → Fin Lidx → ℕ)` is that space, and `p.1`/`p.2` are the volume
oracle's coins and the run's trajectory at the *same* sample point.

**The one extra hypothesis, named.** `κ` is the map "coins ↦ the law the run has
at those coins", `hκ : ∀ c, κ c = trajLaw (θ c)`. Bundling it as a
`ProbabilityTheory.Kernel` assumes exactly one thing beyond
`Ttc.volume_estimate_joint`: that this map is **measurable** in `c`. That is a
regularity condition on `θ`, not a probabilistic claim, and it is what a joint
space costs — without it `volAlg.μ ⊗ₘ κ` does not exist as a measure. It is not
vacuous: `Ttc.kernelOfDiscrete` supplies it for any discrete coin space, in
particular for `Ttc.VolumeAlgorithm.exact`, whose coin space is `Unit`.

No measurability of the *success set* is used anywhere:
`Ttc.le_compProd_apply_of_forall` bounds `(volAlg.μ ⊗ₘ κ) S` from below by the
iterated integral for an arbitrary `S`. -/
theorem volume_estimate_joint_compProd
    (ε δ : ℝ) (hε0 : 0 < ε) (hε1 : ε ≤ 1) (hδ0 : 0 < δ) (hδ1 : δ ≤ 1)
    (atoms : A → LinAtom n) (M : A → Set (Space n)) (M_eq : M = fun a => (atoms a).halfspace)
    (φ : BForm A) (toDNF : BForm A → DNF A)
    (isDNF : IsDNFOf (toDNF φ) φ) (isPositive : DNF.IsPositive (toDNF φ))
    (P : Params) (eps_eq : P.ε = ε) (delta_eq : P.δ = δ) (dim_eq : P.n = n)
    (cubes_le : (Nat.card {c : Cube A // c ∈ toDNF φ} : ℝ) ≤ P.m)
    (facets_le : (Nat.card (FacetIndex (toDNF φ)) : ℝ) ≤ P.r)
    (normal_ne_zero : ∀ j : FacetIndex (toDNF φ), 0 < ∑ k, (atoms j.2.val.atom).coeff k ^ 2)
    (cen : {c : Cube A // c ∈ toDNF φ} → Space n) (gammaHat : ℝ) (hgammaHat : 0 < gammaHat)
    (ball_subset : ∀ i, Metric.ball (cen i) gammaHat ⊆ region M i.val)
    (volume_ne_top : ∀ i : {c : Cube A // c ∈ toDNF φ}, volume (region M i.val) ≠ ⊤)
    (ρ : ℤ) (rho_eq : ρ = P.precision gammaHat)
    (L : ℝ) (L_eq : L = normalisedCount M φ ρ)
    (Lidx : ℕ) (ptE : Fin Lidx → Space n) (ptE_inj : Function.Injective ptE)
    (ptE_mem : ∀ s, ptE s ∈ sol M φ ∩ fineLattice n (latticeScale ρ))
    (ptE_onto : ∀ x ∈ sol M φ ∩ fineLattice n (latticeScale ρ), ∃ s, ptE s = x)
    (volAlg : VolumeAlgorithm n)
    (θ : volAlg.Ω → Fin Lidx → ℝ) (vol : volAlg.Ω → Cube A → ℝ)
    (sampD : Cube A → Space n → ℝ)
    (sampler : KV97Sampler A n M (toDNF φ) ρ P.epsPrime sampD)
    (theta_eq : ∀ (c : volAlg.Ω) (s : Fin Lidx), ∃ i, i ∈ toDNF φ ∧ ptE s ∈ region M i ∧
      θ c s = sampD i (ptE s) * vol c i)
    (cover : Space n → Cube A → Bool) (memPt : Cube A → Fin Lidx → Bool)
    (memPt_eq : ∀ i ∈ toDNF φ, ∀ s, memPt i s = true ↔ ptE s ∈ region M i)
    (cover_eq : ∀ s i, cover (ptE s) i = memPt i s)
    (gen_mem : ∀ (c : volAlg.Ω) (t : ℕ → Fin Lidx → ℕ) (i : Cube A) (j N : ℕ), i ∈ toDNF φ →
      ∀ s ∈ (trajOracles ptE_inj (vol c) cover memPt t).gen i j N ρ,
        s ∈ region M i ∩ fineLattice n (latticeScale ρ))
    (volED_eq : ∀ (c : volAlg.Ω) (i : Cube A) (hi : i ∈ toDNF φ), vol c i =
      gammaHat ^ n * volAlg.est (roundBody (cen ⟨i, hi⟩) gammaHat (region M i))
        P.epsPrime P.deltaPrime c)
    (G : Set volAlg.Ω) (hGmeas : MeasurableSet[volAlg.mΩ] G)
    (hGprob : 1 - δ / 4 ≤ (volAlg.μ G).toReal)
    (hGgood : ∀ c ∈ G, ∀ i ∈ toDNF φ, vol c i ∈ relErr P.epsPrime (volume (region M i)).toReal)
    (vol_pos : ∀ c ∈ G, ∀ i ∈ toDNF φ, 0 < vol c i)
    (big : ∀ c ∈ G, (1 - P.epsPrime) * P.thresh / 8 ≤ ∑ s, θ c s)
    (κ : @ProbabilityTheory.Kernel volAlg.Ω (ℕ → Fin Lidx → ℕ) volAlg.mΩ inferInstance)
    (hκ : ∀ c, κ c = trajLaw (θ c)) :
    1 - δ - δ / 4 ≤
      ((@MeasureTheory.Measure.compProd volAlg.Ω (ℕ → Fin Lidx → ℕ) volAlg.mΩ inferInstance
          volAlg.μ κ)
        {p : volAlg.Ω × (ℕ → Fin Lidx → ℕ) |
          ttcOutput P (fun t => trajOracles ptE_inj (vol p.1) cover memPt t) toDNF ρ φ p.2
            ∈ relErr ε (volSol M φ)}).toReal := by
  letI := volAlg.mΩ
  haveI := volAlg.isProb
  haveI : ProbabilityTheory.IsMarkovKernel κ :=
    ⟨fun c => by rw [hκ c]; exact isProbabilityMeasure_trajLaw (θ c)⟩
  refine toReal_compProd_ge_of_lintegral_ge volAlg.μ κ _ ?_
  have hmain := volume_estimate_joint ε δ hε0 hε1 hδ0 hδ1 atoms M M_eq φ toDNF isDNF isPositive
    P eps_eq delta_eq dim_eq cubes_le facets_le normal_ne_zero cen gammaHat hgammaHat
    ball_subset volume_ne_top ρ rho_eq L L_eq Lidx ptE ptE_inj ptE_mem ptE_onto volAlg θ vol
    sampD sampler theta_eq cover memPt memPt_eq cover_eq gen_mem volED_eq G hGmeas hGprob
    hGgood vol_pos big
  refine le_trans hmain (le_of_eq ?_)
  congr 1
  exact lintegral_congr fun c => by rw [hκ c]; rfl

end Joint

/-! ## Axiom profile

Every declaration of this file, checked transitively (`CLAUDE.md` §4). Expect
`[propext, Classical.choice, Quot.sound]` throughout. -/

#print axioms toReal_lintegral_ge_of_cond
#print axioms le_compProd_apply_of_forall
#print axioms toReal_compProd_ge_of_lintegral_ge
#print axioms kernelOfDiscrete
#print axioms TtcProb.volume_estimate_traj
#print axioms measurableSet_volGood
#print axioms mem_relErr_of_mem_volGood
#print axioms measure_volGood_ge_of_length
#print axioms volume_estimate_joint
#print axioms volume_estimate_joint_compProd

end Ttc

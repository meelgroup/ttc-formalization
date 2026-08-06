# How to audit this formalisation

`lake build` being green and `#print axioms` returning
`[propext, Classical.choice, Quot.sound]` proves that the development has **no
holes**. Neither proves that it states the **right theorem about the right
object**. That check is human-only, and this file is designed to let you make it
in a few minutes without reading a single hard proof.

Everything you need is in [`Ttc/Model/`](Ttc/Model/) — four files, no proofs
worth the name. Nothing in `Model/` refers to a definition outside `Model/`
except Mathlib, so you never have to follow a name into the proof directories to find out
what it means.

---

## 1. Is the capstone about the real object?

Read only the **type** of one declaration — everything before the `:=`.

**[`Ttc.TtcProb.volume_estimate`](Ttc/Model/Theorem.lean#L41)** — `thm:volumettc`:

```lean
theorem Ttc.TtcProb.volume_estimate (T : TtcProb A n) :
    1 - T.δ ≤
      (T.μ {ω | ttcOutput T.P T.O T.toDNF T.ρ T.φ ω
        ∈ relErr T.ε (volSol T.M T.φ)}).toReal
```

*With probability at least `1 − δ`*, the algorithm's output lies in
`(1 ± ε)·Vol(F)`. Four things make that a claim rather than a shape:

* **The measured thing is the algorithm — with three deviations, listed below.**
  [`ttcOutput`](Ttc/Model/Pseudocode.lean#L199) is
  [`Ttc.run`](Ttc/Model/Pseudocode.lean#L183), the line-by-line transcription of
  `alg:ttc`, with the oracles drawn at `ω`. Read `Model/Pseudocode` against
  `sections/algo.tex`; the control flow is the whole algorithm and there is no
  second model it is quietly swapped for. **But the sampling interface is not
  verbatim**, and this is the one place where "the measured thing is the
  algorithm" needs qualifying:

  | Deviation | `algo.tex` | Here | Content? |
  | --- | --- | --- | --- |
  | both `while` loops as exit levels | lines 32–35, 39–42 | `haltLevel`, `absorbLevel` (an `sInf`) | **No**, where the loop terminates: the exit level is what the loop computes. On a run where the second loop never exits, the model says "stay put" — a corner nothing depends on (deviation (b) in `Model/Pseudocode`). |
  | `thin` reads a level, not a coin | lines 33, 40 | `thin j₀ j' X` | **No.** `p` only decreases, so each level is reached at most once per run; a read-off at the target level is a bijection with iterating the coin. |
  | `pois` told the cube and level | line 38, 41 | `pois i j λ` | **Yes.** |
  | `gen` told the cube and level | line 43 | `gen i j N ρ` | **Yes.** |

  The last two are genuine: `GenerateSamples(P(cᵢ), Nᵢ, ρ)` and `Pois(t·p)` are
  *rate-blind* in the paper. They are level-aware here because `lem:numlattice`'s
  `Err(j)` must be an event about a level-`j` process coupled to the run, and a
  rate-blind sampler provably cannot realise that coupling — README finding 15.
  This is no longer a hypothetical: the coupling is now built, it uses the extra
  arguments, and — unlike in the previous version of this file — it is
  **load-bearing for the headline**.
  [`Ttc.trajOracles`](Ttc/Coupling/Family.lean#L397) is an `Ttc.Oracles` bundle
  answering every call by reading a trajectory of the level family,
  [`Ttc.card_run_eq_sum_traj`](Ttc/Coupling/Run.lean#L237) proves the run
  driven by it satisfies `|𝒳| = ∑ₛ ω(J)ₛ` pathwise, and the `oracle_eq` field of
  `Ttc.TtcProb` asserts that the instance's own oracles *are* that bundle.
  **An auditor should read the headline as being about a version of `TTC` whose
  sampler knows which epoch it is in, and whose randomness is the coupled
  Poisson/thinning family.** Whether that is the same algorithm is a judgement
  the reader must make; it is not a difference the machine can see.
* **The target is `Vol(F)`, not a surrogate.**
  [`Ttc.volSol M φ = (volume (sol M φ)).toReal`](Ttc/Model/Prelude.lean#L173) —
  Mathlib's Lebesgue measure of the set of real points satisfying the formula. No
  discretisation, no rational grid.
* **That set is what the algorithm enumerates.**
  [`Ttc.TtcProb.sol_eq_union`](Ttc/Capstone.lean#L113) says
  `⋃ c ∈ T.D, region T.M c = sol T.M T.φ` — `thm:decomposition`, *proved* from the
  `isDNF` field via
  [`Ttc.sol_eq_iUnion_region`](Ttc/Lattice/Decomposition.lean#L112).
* **The interval is the paper's.**
  [`relErr ε b = Set.Icc ((1−ε)b) ((1+ε)b)`](Ttc/Model/Prelude.lean#L181), and
  `T.μ` is a probability measure (field `isProb`).

---

## 2. What is assumed? Read the fields of `TtcProb`

Every global hypothesis is a field of
[`Ttc.TtcProb`](Ttc/Model/ProblemSetting.lean#L43). There are no others: the
theorem quantifies over the structure and adds nothing — no side hypothesis, no
`variable`, no instance argument carrying content.

**No lemma of the paper is assumed outright any more, and no field asserts a
probability bound.** `lem:lattice` used to be two fields; it is now *proved*
([`Ttc.TtcProb.lattice_lo`](Ttc/Lattice/Assembled.lean#L222),
[`lattice_hi`](Ttc/Lattice/Assembled.lean#L227)) from the geometric
fields below, which are hypotheses about the **input**, not about the analysis.
`lem:numlattice` used to be one more field, then a weaker `numlattice_union`
field asserting only the epoch covering. **Both are now theorems**
([`Ttc.TtcProb.numlattice`](Ttc/Coupling/NumLattice.lean#L53),
[`Ttc.TtcProb.numlattice_union`](Ttc/Coupling/Transfer.lean#L267) — the
latter carries the deleted field's statement verbatim, so you can diff it against
an older checkout).

**What replaced the field is 19 fields describing the sampler** (the last block of
the table). They say *what the algorithm's randomness is*, not how often it
fails. That is a real reduction in what is assumed — an assumed conclusion about
probabilities has become an assumed description of a construction, and everything
quantitative is derived from it — but it is **not zero**, and §4 says why.

**Five of those fields have since gone too, and their replacement is weaker.**
`jstar`, `hjstar`, `rate_small`, `rate_le` and `lamStar_ge` used to make an
instance hand over a *chosen epoch index* together with both ends of its rate
window. `j*` is now **constructed** inside
[`Ttc.TtcProb.numlattice_union`](Ttc/Coupling/Transfer.lean#L267) by
[`Ttc.exists_epoch`](Ttc/Coupling/Transfer.lean#L140): the window
`[(1−ε')·Thresh/8, Thresh/2]` has ratio at least `4`, so halving from `∑θ` cannot
step over it. Deleting a chosen existential from a hypothesis bundle is a
stronger move than deleting an inequality — the instance no longer picks the
epoch the estimate is evaluated at. Two new theorems carry it:
[`Ttc.TtcProb.thresh_pos`](Ttc/Coupling/Transfer.lean#L242) (`Thresh > 0`
from `alg:ttc` line 20's own formula, previously implicit) and
[`Ttc.TtcProb.vol_le_total`](Ttc/Coupling/Transfer.lean#L260) (a cube's
rate is at most the total). `rate_small` then follows from `vol_pos` and
`vol_le_total` by
[`Ttc.rate_small_of_epoch`](Ttc/Coupling/Transfer.lean#L180). What was
added in exchange is three fields — `vol_eq`, `vol_pos`, `big` — and `vol_eq`
**closes a gap** rather than renaming one: before it, nothing tied the run's
volume estimates to the instance at all, and `rate_small` was the only field
standing between `vol` and nonsense.

Each field's line number is a link; the whole structure runs
[43](Ttc/Model/ProblemSetting.lean#L43)–[175](Ttc/Model/ProblemSetting.lean#L175),
about 135 lines of declarations and docstrings, so reading it end to end is also
an option.

| Field | Line | What it asserts | Status |
| --- | --- | --- | --- |
| `ε`, `δ`, `hε0`, `hε1`, `hδ0`, `hδ1` | [45](Ttc/Model/ProblemSetting.lean#L45)–[55](Ttc/Model/ProblemSetting.lean#L55) | `ε, δ ∈ (0,1]` | the theorem's own parameters |
| `atoms`, `M`, `M_eq` | [57](Ttc/Model/ProblemSetting.lean#L57)–[62](Ttc/Model/ProblemSetting.lean#L62) | each atom is a linear constraint `A x ≤ b`, and `M` interprets it as that half-space | **assumed of the input** — this is what "SMT(LRA)" means |
| `φ`, `toDNF` | [64](Ttc/Model/ProblemSetting.lean#L64), [68](Ttc/Model/ProblemSetting.lean#L68) | the Boolean abstraction of `F` (line 15), and the circuit-AllSAT procedure (line 16) | `φ` with `atoms` **is** the input formula; the DNF is *computed* from it, not a second input |
| `isDNF` | [71](Ttc/Model/ProblemSetting.lean#L71) | `toDNF φ` and `φ` agree on every Boolean assignment | **assumed** of the external `ToDNF`/AllSAT tool — the one thing line 16 is trusted for. `thm:decomposition` is *proved* from it |
| `isPositive` | [71](Ttc/Model/ProblemSetting.lean#L71) | no literal of `D` is negated | **assumed of the input** — see §4 and README finding 5 |
| `Ω`, `mΩ`, `μ`, `isProb` | [73](Ttc/Model/ProblemSetting.lean#L73)–[79](Ttc/Model/ProblemSetting.lean#L79) | a probability space for the algorithm's randomness | structure, not an assumption |
| `P`, `eps_eq`, `delta_eq`, `dim_eq` | [81](Ttc/Model/ProblemSetting.lean#L81)–[87](Ttc/Model/ProblemSetting.lean#L87) | the parameter block, run at the theorem's own `ε` and `δ` and in the ambient dimension | inputs + three ties that used to be missing |
| `cubes_le`, `facets_le` | [89](Ttc/Model/ProblemSetting.lean#L89), [91](Ttc/Model/ProblemSetting.lean#L91) | `m` bounds the number of cubes, `r` the number of facets | **assumed of the input**; the paper's `m`, `r` |
| `normal_ne_zero` | [93](Ttc/Model/ProblemSetting.lean#L93) | every facet's normal vector is nonzero | **assumed of the input**; a zero normal is not a facet |
| `O` | [95](Ttc/Model/ProblemSetting.lean#L95) | the `ω`-indexed oracle bundle | input; pinned by `oracle_eq` below |
| `cen`, `gammaHat`, `hgammaHat`, `ball_subset` | [99](Ttc/Model/ProblemSetting.lean#L99)–[107](Ttc/Model/ProblemSetting.lean#L107) | each `P(cᵢ)` contains an `ℓ₂`-ball of radius `γ̂ > 0` about its own centre | **assumed of the input** — `lem:nonconv`'s own hypothesis, in the paper's words. The LP of `alg:prec` that computes `γ̂` is **not modelled** |
| `volume_ne_top` | [109](Ttc/Model/ProblemSetting.lean#L109) | each `P(cᵢ)` has finite volume | **assumed of the input** — the paper leaves it implicit |
| `ρ`, `rho_eq` | [112](Ttc/Model/ProblemSetting.lean#L112), [114](Ttc/Model/ProblemSetting.lean#L114) | the precision is `GetPrecision`'s output, `ρ = ⌈log₁₀(γ/γ̂)⌉` | `alg:prec` line 91, transcribed — and now **load-bearing**, see §4 |
| `gen_mem` | [119](Ttc/Model/ProblemSetting.lean#L119) | `GenerateSamples` returns points of `P(cᵢ) ∩ 𝕃ⁿ` | **assumed of the external sampler** — `Ttc.Oracles` fixes only *how many* it returns. Not distributional |
| `L`, `L_eq` | [122](Ttc/Model/ProblemSetting.lean#L122), [124](Ttc/Model/ProblemSetting.lean#L124) | `L` **is** `\|Sol(F) ∩ 𝕃ⁿ\|/10^(ρn)` ([`normalisedCount`](Ttc/Model/Prelude.lean#L166)) | definition, not an assumption |
| **— from here the 19 fields describe the sampler —** | | | |
| `Lidx`, `ptE`, `ptE_inj` | [133](Ttc/Model/ProblemSetting.lean#L133), [135](Ttc/Model/ProblemSetting.lean#L135), [137](Ttc/Model/ProblemSetting.lean#L137) | the lattice points the coupled family is indexed by, and an injective enumeration of them | **assumed of the sampler** — structure of the model |
| `θ`, `θ_nonneg`, `θ_pos` | [139](Ttc/Model/ProblemSetting.lean#L139), [141](Ttc/Model/ProblemSetting.lean#L141), [143](Ttc/Model/ProblemSetting.lean#L143) | each point's level-`0` Poisson rate, nonnegative, with **positive total** | **assumed** — `θ_pos` also rules out the empty instance, which is why the old degenerate witness died |
| `vol`, `cover`, `memPt` | [145](Ttc/Model/ProblemSetting.lean#L145), [147](Ttc/Model/ProblemSetting.lean#L147), [149](Ttc/Model/ProblemSetting.lean#L149) | the rate the run draws each cube with, its coverage test, and cube membership on the enumerated points | inputs to the oracle bundle — but `vol` is no longer free: `vol_eq` below pins it |
| `toTraj`, `toTraj_meas` | [151](Ttc/Model/ProblemSetting.lean#L151), [153](Ttc/Model/ProblemSetting.lean#L153) | each `ω` reads as a trajectory `ℕ → Fin Lidx → ℕ`, measurably | structure |
| **`law_eq`** | [155](Ttc/Model/ProblemSetting.lean#L155) | **`μ.map toTraj = trajLaw θ`** — the randomness **is** the coupled level family ([`Ttc.trajLaw`](Ttc/Coupling/Family.lean#L209)) | **assumed of the sampler — the strongest field on this page.** Not "the draws are Poisson"; "the draws are *this construction*" |
| **`oracle_eq`** | [157](Ttc/Model/ProblemSetting.lean#L157) | **`O ω = trajOracles ptE_inj vol cover memPt (toTraj ω)`** — the oracles answer by reading that trajectory | **assumed of the sampler**; pins `O` completely |
| `cover_eq`, `cover_all` | [159](Ttc/Model/ProblemSetting.lean#L159), [161](Ttc/Model/ProblemSetting.lean#L161) | the coverage test agrees with cube membership on the lattice; the cubes cover every enumerated point | **assumed** — combinatorial, checkable of an instance |
| **`vol_eq`**, `vol_pos` | [165](Ttc/Model/ProblemSetting.lean#L165), [167](Ttc/Model/ProblemSetting.lean#L167) | **`∑_{s : memPt i s} θ s = vol i`** for every cube `i ∈ D`, and `0 < vol i` — each cube's rate *is* the total level-`0` rate of the points it covers | **assumed of the sampler**, and it **closes a gap**: before it, nothing at all related the run's volume estimates to the instance. `Ttc.TtcProb.vol_le_total` reads `vol i ≤ ∑θ` off it |
| **`big`** | [172](Ttc/Model/ProblemSetting.lean#L172) | **`(1−ε')·Thresh/8 ≤ ∑θ`** — the instance is large enough for the sketch to be worth running | **assumed of the instance**, and a genuine assumption — but it is the paper's own regime, not an artifact. It is what `Ttc.exists_epoch` needs to build `j*`, and [`Ttc.Box.boxProb`](Ttc/Witness/BoxProb.lean#L271) arranges it by choosing the box side from `Thresh` |
| **`theta_lo`, `theta_hi`** | [`ProblemSetting`](Ttc/Model/ProblemSetting.lean) | **`(1−ε')²(1−η)/10^(ρn) ≤ θ s ≤ (1+ε')²(1+η)/10^(ρn)`** — the paper's Invariant, per lattice point | **assumed of the sampler** — the only place the geometry meets the probability. It replaced the exact `∑θ = L` this row used to carry, and it is now genuinely two-sided: [`Ttc.window_of_two_sided`](Ttc/Coupling/Transfer.lean#L104) is what consumes it |

**Almost-uniform sampling, `eq:sampler`.** `GenerateSamples` is assumed only to
draw from a distribution `D` over `P(cᵢ) ∩ 𝕃ⁿ` that is pointwise within a
`(1±ε')` factor of uniform — not from the uniform distribution itself. An auditor
should note where that assumption lives: **nowhere as a field of its own.** Its
entire content is the extra `(1±ε')` factor in `theta_lo`/`theta_hi`, because the
model already gave each lattice point its own rate `θ s`, and a per-point rate is
exactly what an almost-uniform sampler produces. So the thing to check here is
not a new hypothesis but a *widened* one: the window is weaker than it was, which
makes the theorem stronger, and the headline statement is untouched.

Two consequences an auditor should verify rather than assume: the accuracy
budget is now `(1±ε')³(1±η) ⊆ (1±ε/2)`
([`Ttc.Params.epsPrime_window`](Ttc/Constants/Parameters.lean#L187)) — `ε/3` no
longer suffices — and `δ' = δ/(4m)`
([`Ttc.Params.deltaPrime`](Ttc/Model/Prelude.lean)), which is what pays for the
sampler's failure event `E_samp` beside `Vol_ED`'s `E_vol`. Neither is
load-bearing for a *hole* in the proof; both are transcriptions of `alg:ttc`.

A one-sided bound would **not** do, and this is the one place where the paper's
choice of `≤` versus a two-sided window is doing real work: from
`D(x) ≤ (1+ε')/|P ∩ 𝕃ⁿ|` alone one gets only `D(A) ≥ |A|/|P ∩ 𝕃ⁿ| − ε'`, an
additive loss that is vacuous exactly when `A` is the small part of `P(cᵢ)` no
later cube covers — which is the mass the estimate is made of. `theta_lo` would
be unprovable and the lower half of the headline would fail.

There is **no `jstar` row any more**, and that is the point: an epoch index in
the right window used to be five fields of this table, and is now produced by
[`Ttc.exists_epoch`](Ttc/Coupling/Transfer.lean#L140) from `big` and
[`Ttc.TtcProb.thresh_pos`](Ttc/Coupling/Transfer.lean#L242).
[`Ttc.Box.exists_jstar`](Ttc/Witness/BoxProb.lean#L221) still exists in the
witness file but is now **unused**.

The README's [What is assumed](README.md#what-is-assumed) says the same at
length, with the exact list of what *is* proved about each.

**Where the `δ` comes from.** It is not hand-waved, and it is no longer even
conditional on an assumed covering. The sampler fields give the covering
([`Ttc.TtcProb.numlattice_union`](Ttc/Coupling/Transfer.lean#L267), proved
via [`Ttc.numlattice_union_of_model`](Ttc/Coupling/Transfer.lean#L35) from
[`Ttc.traj_numlattice_le`](Ttc/Coupling/Run.lean#L685)); the covering plus
the *proved* sizes of the three contributions
([`Ttc.numlattice_failure_le`](Ttc/Process/SketchProcess.lean#L246), at the
algorithm's own `Thresh` and `δ'`) gives `Pr[ output ∈ (1±ε/2)·L ] ≥ 1 − δ`
([`Ttc.TtcProb.numlattice`](Ttc/Coupling/NumLattice.lean#L53)); the deterministic
chain shows that event is *contained in* the `(1±ε)·Vol(F)` event; measure
monotonicity does the rest. The `δ` is earned — given that the sampler is the one
`law_eq` and `oracle_eq` describe.

Nothing anywhere here is about running time (`thm:runtime` is out of scope).

---

## 3. Is the theorem non-vacuous?

A `∀ (T : TtcProb A n), …` proves nothing if `TtcProb` is uninhabited.

[`Ttc.Box.nonempty_ttcProb`](Ttc/Witness/BoxProb.lean#L349), witnessed by
[`Ttc.Box.boxProb`](Ttc/Witness/BoxProb.lean#L271): **the box `[0,c]ⁿ`**, cut out
by `2n` positive linear atoms ([`Ttc.boxAtoms`](Ttc/Witness/Box.lean#L47)) as
the single cube of a one-cube DNF
([`Ttc.boxCube`](Ttc/Witness/Box.lean#L270),
[`Ttc.boxDNF`](Ttc/Witness/Box.lean#L307)) representing the conjunction of
those atoms ([`Ttc.boxForm`](Ttc/Witness/Box.lean#L387),
[`Ttc.boxDNF_isDNFOf`](Ttc/Witness/Box.lean#L414)), sampled by the coupled
family. It needs `1 ≤ n`, because `Ttc.Params` requires a positive dimension and
`dim_eq` ties it to the ambient one.

**It is NOT degenerate, and that is the point.** Check these four things:

* **Nonempty solution set, positive volume.**
  `Sol(F) = [0,c]ⁿ` ([`Ttc.sol_boxForm`](Ttc/Witness/Box.lean#L429)), a
  genuine polytope. The geometric fields are exercised, not vacuous:
  `ball_subset` is discharged by
  [`Ttc.ball_subset_region_boxCube`](Ttc/Witness/Box.lean#L334) (the
  inscribed ball of radius `c/2` about the centre), `volume_ne_top` by
  [`Ttc.volume_region_boxCube_ne_top`](Ttc/Witness/Box.lean#L342),
  `isPositive` by [`Ttc.boxDNF_isPositive`](Ttc/Witness/Box.lean#L310), and
  `normal_ne_zero` by
  [`Ttc.boxAtoms_normal_ne_zero`](Ttc/Witness/Box.lean#L324).
* **`L` is large, not zero.** The side is chosen as
  `c = max 1 Thresh` ([`Ttc.Box.side`](Ttc/Witness/BoxProb.lean#L98)), and
  [`Ttc.Box.side_le_Lval`](Ttc/Witness/BoxProb.lean#L161) proves
  `Thresh ≤ c ≤ cⁿ ≤ L`, from
  [`Ttc.normalisedCount_box_ge`](Ttc/Witness/Box.lean#L451) — which holds at
  *every* precision `ρ`, so `c` may be picked before `ρ` is fixed. The instance
  therefore clears the regime the epoch estimate needs — that is exactly the
  `big` field, discharged at
  [BoxProb:343](Ttc/Witness/BoxProb.lean#L343) from
  [`Ttc.Box.epsPrime_thresh_le_Lval`](Ttc/Witness/BoxProb.lean#L210).
* **The sampler fields are discharged by proof, not by an empty failure event.**
  `Ω` *is* the trajectory space, `μ` is `trajLaw θ`, `toTraj` is the identity, so
  `law_eq` is `Measure.map_id` and `oracle_eq` is `rfl`; the run is therefore a
  genuinely random one, and `Ttc.TtcProb.numlattice_union` instantiated here is
  the real bound (its self-coupled form is
  [`Ttc.numlattice_union_of_traj`](Ttc/Coupling/Transfer.lean#L190)). The
  two newest fields are discharged too, not dodged: `vol_eq`
  ([BoxProb:336](Ttc/Witness/BoxProb.lean#L336)) holds because the single cube
  covers every enumerated point, so the filtered sum is `∑θ = L = vol`, and
  `vol_pos` ([BoxProb:342](Ttc/Witness/BoxProb.lean#L342)) is `Lval_pos`.
* **The rates spread `L` evenly, so `∑θ = L` exactly.**
  [`Ttc.Box.th`](Ttc/Witness/BoxProb.lean#L188) is the constant `L/Lidx` and
  [`Ttc.Box.sum_th`](Ttc/Witness/BoxProb.lean#L195) proves the total is `L`. This
  is the **ideal instance** CLAUDE.md §13 asks for: every error coefficient is
  `0`, `Vol_ED` returns the exact volume
  ([`Ttc.Box.vl`](Ttc/Witness/BoxProb.lean#L242)), and the accuracy window is
  discharged with nothing to spend
  ([`Ttc.window_of_exact`](Ttc/Coupling/Transfer.lean#L121)).

The old witness `Ttc.trivialProb` (empty DNF, `L = 0`, everything vacuous) has
been **deleted**. It could not survive the sampler fields: `D = []` forces
`Lidx = 0`, which contradicts `θ_pos`. That is exactly the point of carrying
those fields — the structure can no longer be inhabited by an instance that does
nothing.

`TtcProb` is the only hypothesis-bundling structure the capstone quantifies over.
(`Ttc.TtcAnalysis` in [`Capstone`](Ttc/Capstone.lean#L44) is an
internal device for the arithmetic, not part of the statement.)

`TtcProb` is now the **only** hypothesis-bundling structure in the development.
An alternative primitive-by-primitive oracle contract (`Ttc.OracleLaws`: `pois` is
Poisson, `halve` thins each multiplicity `Binomial(·,½)`) used to be stated here
with **no witness**; it has been **deleted**, together with the draw-counter
machinery it was phrased over. It was consumed by nothing, so no theorem changes,
and there is no longer an uninhabited bundle for a future theorem to be vacuous
over.

---

## 4. Where a name stands in for a proof

`#print axioms` cannot see a definition whose *name* claims more than its body
proves. These are the residual assumptions of that kind. None is hidden — each is
stated in the file that introduces it — but they are collected here because they
are exactly what a green build does not certify.

**The `numlattice_union` field is GONE.** The previous version of this page said
it was the one remaining assumption of this kind and was still present; that is
no longer true. It has been deleted from `Ttc.TtcProb`, and the same statement —
verbatim — is now the theorem
[`Ttc.TtcProb.numlattice_union`](Ttc/Coupling/Transfer.lean#L267). No field
of `Ttc.TtcProb` asserts a probability bound any more.

**What stands in its place is a description, and that is where the residual
assumption now lives.** The `law_eq` and `oracle_eq` fields
([ProblemSetting:155](Ttc/Model/ProblemSetting.lean#L155),
[157](Ttc/Model/ProblemSetting.lean#L157)) are the sharpest case on this page of
"a name doing work no lemma checks" — not because a `def`'s name overreaches, but
because two `def`s ([`Ttc.trajLaw`](Ttc/Coupling/Family.lean#L209),
[`Ttc.trajOracles`](Ttc/Coupling/Family.lean#L393)) are *asserted to be the
implementation*. They are honest about what they are: every property either one
is used for is proved (see the table at the end of this section). What no proof
can establish is that a real `TTC` implementation's sampler equals them. So:

> **An auditor should read the headline as: given that `TTC`'s randomness is the
> coupled Poisson/thinning family read through `trajOracles`, its output is
> within `(1±ε)·Vol(F)` with probability `≥ 1−δ`.** The conditional is a
> modelling claim about the sampler, not an unproved probability estimate. That
> is a strictly better position than the previous one — where the *conclusion* of
> the paper's hardest lemma was assumed — but it is not "assumption-free".

Two smaller commitments inside the same block are worth naming: `rate_eq_L`
assumes `∑θ = L` **exactly** (the general two-sided version
[`Ttc.window_of_two_sided`](Ttc/Coupling/Transfer.lean#L104) exists and is
unused), and `big` assumes `(1−ε')·Thresh/8 ≤ ∑θ` — the instance is in the regime
the sketch is for. Both are real assumptions. `big` is *not* an artifact of the
formalisation: it is the paper's own regime, and it is what
[`Ttc.Box.boxProb`](Ttc/Witness/BoxProb.lean#L271) arranges by choosing the box
side from `Thresh`.

**The `jstar` block is gone, and that is the sharper improvement.** It used to
assume an epoch index in the right window *exists* for the instance — five
fields, one of them a chosen `j*` and the rest its window. `Ttc.exists_epoch`
now proves such an index exists for *every* instance satisfying `big`, so the
proof no longer takes the epoch it evaluates at from the hypothesis bundle.
Its hypotheses are exactly `0 < Thresh`, `0 ≤ ε'` and `big` — it does **not**
need `0 < ∑θ`, so nothing in the construction of `j*` leans on `θ_pos`.
[`Ttc.Box.exists_jstar`](Ttc/Witness/BoxProb.lean#L221) remains in the witness
file but nothing consumes it.

**Two facts the deletion needed, both now theorems.**
[`Ttc.TtcProb.thresh_pos`](Ttc/Coupling/Transfer.lean#L242) proves
`Thresh > 0` from `alg:ttc` line 20's own formula rather than leaving it implicit
— `δ ≤ 1` forces `log(24/δ) ≥ log 24 > 0`, and `ε' = ε/12 ∈ (0, 1/12]` keeps
`(1−ε')ε'²` positive — and
[`Ttc.TtcProb.vol_le_total`](Ttc/Coupling/Transfer.lean#L260) proves each
cube's rate is at most the total, since `vol_eq` sums a subset of nonnegative
rates. Together with `vol_pos` they feed
[`Ttc.rate_small_of_epoch`](Ttc/Coupling/Transfer.lean#L180), which was
generalised to take a cube rate merely *bounded by* the total, and that is what
replaces the old `rate_small` field.

**No mathematics is missing.** Every
*estimate* the proof invokes is a theorem here, including the one the paper
imports from Soos et al.: `lem:chernoff` is proved from the Poisson moment
generating function upwards
([`Process/Chernoff`](Ttc/Process/Chernoff.lean)), as are both of its
applications, `lem:process`, the epoch series, and the `Vol_ED` failure budget
the paper omits. All four original obstacles to composing them into a statement
about `Ttc.run` are now cleared:

* ~~`Ttc.Oracles` cannot express independence.~~ **Fixed** — calls are now
  level-indexed (see the note above), so independence across levels is statable,
  and `Err(j)`/`Nois(j)` are events about that index.
* ~~`lem:process` is only a pmf identity.~~ **Fixed** —
  [`Ttc.countLaw_eq_pi`](Ttc/Process/PoissonLaws.lean#L91) gives it as an
  identity of measures, with independence, thinning and superposition as
  corollaries.
* ~~The halvings form a stopping time.~~ **Resolved** — and reading the paper's
  invariant as conditioning turns out to be *false* (README finding 14). The
  correct non-adaptive reading is
  [`Ttc.levelLaw`](Ttc/Process/SketchProcess.lean#L55), and both branch
  estimates plus the whole `δ` budget are proved over it
  ([`numlattice_failure_le`](Ttc/Process/SketchProcess.lean#L246)).
* ~~The coupling is missing.~~ **Built** — README finding 15's construction now
  exists. [`Ttc.trajOracles`](Ttc/Coupling/Family.lean#L397) is an honest
  `Ttc.Oracles` bundle (both interface contracts discharged; `gen_card` holds
  unconditionally, via a never-taken filler branch) whose answers are read off a
  trajectory of the coupled level family
  ([`Ttc.trajLaw`](Ttc/Coupling/Family.lean#L209)). Driving the *real*
  `Ttc.run` off it, [`Ttc.card_run_eq_sum_traj`](Ttc/Coupling/Run.lean#L237)
  proves `|𝒳| = ∑ₛ ω(J)ₛ` **pathwise**, at the run's own stopping level `J`, on
  every nested trajectory — and nestedness holds almost surely
  ([`Ttc.trajLaw_ae_nested`](Ttc/Coupling/Run.lean#L516)). That is
  equality of random variables, which is strictly stronger than the equality in
  law `lem:process` supplies and is what the union bound actually needs.
  Assembling it with the transported level estimates,
  [`Ttc.traj_numlattice_le`](Ttc/Coupling/Run.lean#L609) proves
  `lem:numlattice`'s bound for that run outright, with a *smaller* right-hand
  side than the paper's (no `+ δ/2`, no factor `m`). **No probability claim is
  assumed in it**: its hypotheses are `hlo`/`hhi` (supplied by the already-proved
  `lem:lattice`), `hsmall`/`hrate` (conditions on `Thresh` and `vol`), and
  `hall`/`hcov` (the cubes cover the lattice points; the oracle's coverage test
  agrees with cube membership).

* **And the transport off the trajectory model is done.**
  `traj_numlattice_le` is about `trajLaw θ` on `ℕ → (Fin L → ℕ)` with the oracles
  `trajOracles`, whereas `Ttc.TtcProb` carries an arbitrary `Ω`, `μ` and `O`.
  [`Ttc.numlattice_union_of_model`](Ttc/Coupling/Transfer.lean#L35) closes
  that: given `oracle_eq`, the run's failure event is the `toTraj`-preimage of
  the trajectory-space one; `Measure.le_map_apply` bounds its measure by the
  pushforward (no measurability of the event is needed — the inequality runs one
  way); and `law_eq` says that pushforward is `trajLaw θ`. Feeding it the fields
  gives `Ttc.TtcProb.numlattice_union`, which is what deleted the field.

Two further things an auditor should not skip:

* **Termination is not assumed anywhere.** Both `while` loops are modelled as
  exit levels, and one might expect the result to need to know that the second
  loop actually exits. It does not: `traj_numlattice_le` holds whatever level the
  run reaches, because the coupling makes the output a function of that level and
  the `Err` estimate covers every level below the cap. The work is done instead by
  `traj_numlattice_le`'s `hsmall` hypothesis, that no cube's rate still triggers
  the first loop at level `j*−1`. That used to be the `rate_small` field; it is
  now *derived*, from `vol_pos` and `Ttc.TtcProb.vol_le_total` via
  `Ttc.rate_small_of_epoch`. The paper addresses none of this.
* **What the exit-level model says on a non-terminating run.** `Nat.sInf` of an
  empty set is `0`, so if the absorption loop's guard never fails the model has
  the loop stay put rather than diverge. Nothing rests on that branch: every
  consequence drawn from an exit level has the form "every level strictly below it
  had the guard true" ([`lt_haltLevel`](Ttc/Invariants.lean#L69),
  [`lt_absorbLevel`](Ttc/Invariants.lean#L80)), which is vacuous there.
  This is deviation (b) of `Model/Pseudocode`.

**The geometric fields are hypotheses about the input, and they are real.**
`ball_subset`, `volume_ne_top`, `normal_ne_zero`, `isPositive`, `cubes_le`,
`facets_le` are not consequences of anything here; they are what the paper
assumes of the decomposition (`ball_subset` verbatim, the rest implicitly).
Two are worth staring at:
* `isPositive` **excludes negated atoms**, which the paper's algorithm does not.
  A negated atom denotes an *open* half-space, and on a facet hyperplane the
  lattice count of a set and of its closure differ — so this is not a technicality
  volume arguments wash out. See README finding 5. Concretely: `lem:lattice` is
  proved here for positive DNFs only.
* `volume_ne_top` is implied by `ball_subset` plus boundedness, which the paper
  never states. It is assumed rather than derived.

**`L` is now the lattice count, not a bare real.** The `L_eq` field pins it to
[`Ttc.normalisedCount`](Ttc/Model/Prelude.lean#L166) `= |Sol(F) ∩ 𝕃ⁿ|/10^(ρn)`,
and `lem:lattice` is proved about *that*. (Previously `L` was a free real related
to `Vol(F)` only by assumption; that gap is closed.)

**The non-vacuity witness is no longer degenerate.**
[`Ttc.Box.boxProb`](Ttc/Witness/BoxProb.lean#L271) is a genuine polytope with
`L ≥ Thresh`, and its covering obligation is proved rather than vacuous; §3 has
the four things to check. The old degenerate `trivialProb` has been deleted
because the sampler fields exclude it.

**The oracle bundle constrains almost nothing — but `oracle_eq` does.**
[`Ttc.Oracles`](Ttc/Model/Pseudocode.lean#L76) has four external calls as fields.
Only two carry any hypothesis — [`halve_le`](Ttc/Model/Pseudocode.lean#L87)
(thinning returns a sub-multiset) and
[`gen_card`](Ttc/Model/Pseudocode.lean#L101) (`GenerateSamples` returns exactly
`N` points, for every precision `ρ`). Nothing in the *bundle* states that `vol`
is an `(1±ε')`-accurate volume estimate, that `pois c λ` is Poisson-distributed,
or that `thin j₀ j'` keeps each element independently with probability
`2^(j₀−j')`. That is deliberate: it is what makes the bundle inhabitable by
[`Ttc.trajOracles`](Ttc/Coupling/Family.lean#L397), the coupling. What supplies
the distributional content is not the bundle but the `oracle_eq` and `law_eq`
fields of `Ttc.TtcProb`, which say the instance's bundle *is* `trajOracles` over
`trajLaw θ`.

**The sampling interface is level-aware; the paper's is not.** §1 tabulates the
four deviations. Two of them (`pois`, `gen` receiving the cube and level) are
real: they change what the modelled algorithm is allowed to do. They are there
because README finding 15 shows the union bound over epochs needs a *pathwise*
coupling between the run and a level-`j` process, `lem:process` supplies only
equality *in law*, and a rate-blind sampler cannot bridge the two. The coupling
that consumes them now exists (above), which settles that the extra arguments are
*used*, not that a rate-blind version would be false. This is the single most
important thing on this page for a reader deciding how much the headline claims.

**The `level` is not in the pseudocode; `p` is.** `Ttc.SketchState` carries the
level `j` in place of the rate, with `p = 2^(−j)` a definition, and
`thin`/`pois`/`gen` take it as an argument. An auditor comparing against
`algo.tex` will find `p`, not `j`. The index is present because an *unindexed*
oracle cannot model fresh randomness: an unindexed `halve` applied twice to the
same multiset would return the same answer, so a thinning that happened to be a
no-op would freeze `𝒳` forever. Read the level as naming the draw *and* carrying
the paper's `p` — the two are the same information.

**The coupling's definitions carry proving lemmas, not just names.** This is the
part of the development most exposed to the "a `def` whose name claims more than
its body proves" failure, so each of the new names is listed here with the lemma
that earns it:

| `def` | What the name promises | Proved by |
| --- | --- | --- |
| [`Ttc.levelLaw`](Ttc/Process/SketchProcess.lean#L55) | the law of the level-`j` process | [`chainLaw_eq_levelLaw`](Ttc/Process/SketchProcess.lean#L105) — nested thinning from level `0` reproduces it at every `j` |
| [`Ttc.totalRate`](Ttc/Process/SketchProcess.lean#L63) | the total rate at level `j` | definitionally `(∑ θ)/2ʲ`; used only through that |
| [`Ttc.famCount`](Ttc/Coupling/Family.lean#L80), [`Ttc.trajLaw`](Ttc/Coupling/Family.lean#L209) | the coupled family and its law | [`map_trajLaw_eval`](Ttc/Coupling/Family.lean#L274) — coordinate `j` carries exactly `levelLaw θ j`; [`trajLaw_ae_nested`](Ttc/Coupling/Run.lean#L516) — it is a *nested* thinning |
| [`Ttc.trajOracles`](Ttc/Coupling/Family.lean#L397) | oracles that read the family | it is an `Ttc.Oracles`, so both interface contracts are discharged in the definition; that the *run* it drives realises the family is [`card_run_eq_sum_traj`](Ttc/Coupling/Run.lean#L237) |
| [`Ttc.CoupledAt`](Ttc/Coupling/Run.lean#L31), [`Ttc.PoisAt`](Ttc/Coupling/Run.lean#L145) | "the state is the family here" | preserved by every loop operation ([`coupledAt_thin`](Ttc/Coupling/Run.lean#L63), [`coupledAt_step`](Ttc/Coupling/Run.lean#L164), [`coupledAt_foldl`](Ttc/Coupling/Run.lean#L215)) and read off by [`count_of_coupledAt`](Ttc/Coupling/Run.lean#L43) |
| [`Ttc.haltLevel`](Ttc/Model/Pseudocode.lean#L154), [`Ttc.absorbLevel`](Ttc/Model/Pseudocode.lean#L161) | "the level the `while` loop exits at" | [`le_haltLevel`](Ttc/Invariants.lean#L60)/[`le_absorbLevel`](Ttc/Invariants.lean#L63) — it is at or above the entry level; [`lt_haltLevel`](Ttc/Invariants.lean#L69)/[`lt_absorbLevel`](Ttc/Invariants.lean#L80) — every level strictly below it had the loop's guard true |
| [`Ttc.Box.Lval`](Ttc/Witness/BoxProb.lean#L157) | the witness's normalised lattice count | it is `Ttc.normalisedCount` by definition, and [`Ttc.Box.side_le_Lval`](Ttc/Witness/BoxProb.lean#L161) proves `Thresh ≤ c ≤ L` from [`Ttc.normalisedCount_box_ge`](Ttc/Witness/Box.lean#L451) |
| [`Ttc.Box.th`](Ttc/Witness/BoxProb.lean#L188) | the witness's rates | [`Ttc.Box.sum_th`](Ttc/Witness/BoxProb.lean#L195) — they total `L` exactly, which is what `rate_eq_L` demands |

The one place a name is doing work no lemma checks is
[`Ttc.padPoint`](Ttc/Coupling/Family.lean#L391), the filler `trajOracles.gen`
returns when asked for a count the family cannot supply. That branch is never
taken by the run — `gen` is always passed the `N` that `pois` produced — and
nothing downstream depends on what it contains; it exists so that `gen_card`
holds unconditionally.

**`GetPrecision` is a formula, not an algorithm — but it is no longer inert.**
`γ̂` is still an input: the LP of `alg:prec` that computes the largest inscribed
ball, and the loop taking the max over polytopes, are **not modelled**. What *is*
now proved is that the precision it returns is exactly what the accuracy proof
needs: [`Ttc.gamma_le_latticeScale_mul`](Ttc/Lattice/Assembled.lean#L69)
shows `ρ = ⌈log₁₀(γ/γ̂)⌉` makes `10^ρ·γ̂ ≥ γ`, which is what gives the *dilated*
polytopes the inscribed radius `lem:nonconv` requires. So `rho_eq` is
load-bearing: delete it and `lem:lattice` no longer goes through.

**The parameter block is a transcription, checkable only by eye.** The constants
in [`Ttc.Params`](Ttc/Model/Prelude.lean#L191) — `η`, `ε'`, `Thresh`, `κ`, `γ`,
`ρ` — assert by their definitions that they are what `alg:ttc` (lines 17–20) and
`alg:prec` (line 86) compute. Read them beside `sections/algo.tex`. Unlike
before, the *results about* them are now reached by the headline: `κ` and `γ`
enter `lem:lattice` through [`Ttc.Params.shell_factor_bound`](Ttc/Constants/Parameters.lean#L102)
and [`shell_factor_bound_deflated`](Ttc/Constants/Parameters.lean#L144), so
"the constants are verified" and "the main theorem holds" meet for `η`, `κ`, `γ`,
`ρ`. They now meet for `ε'` and `Thresh` as well: `Ttc.TtcProb.numlattice` reads
both off the parameter block and feeds them to
[`Ttc.numlattice_failure_le`](Ttc/Process/SketchProcess.lean#L246), which is what
turns the covering into `1 − δ` — so that lemma, and with it the two `Thresh`
branches, is on the headline's dependency path. Re-check with the probe in §5
rather than taking this on trust.

**Fuel, not termination.** Both `while` loops in `Model/Pseudocode` take an
explicit iteration budget and return the current state when it runs out. No
termination theorem is claimed, and claiming one would be false: the second loop
terminates only with high probability.

---

## 5. Re-checking the machine-checkable part

```bash
lake exe cache get && lake build     # zero "declaration uses 'sorry'" warnings
```

```lean
import Ttc
#print axioms Ttc.TtcProb.volume_estimate
-- [propext, Classical.choice, Quot.sound]
#print axioms Ttc.TtcProb.lattice_lo
-- [propext, Classical.choice, Quot.sound]
#print axioms Ttc.TtcProb.numlattice
-- [propext, Classical.choice, Quot.sound]
#print axioms Ttc.TtcProb.numlattice_union      -- the ex-field
-- [propext, Classical.choice, Quot.sound]
#print axioms Ttc.TtcProb.thresh_pos            -- Thresh > 0, no longer implicit
-- [propext, Classical.choice, Quot.sound]
#print axioms Ttc.TtcProb.vol_le_total          -- a cube's rate ≤ the total
-- [propext, Classical.choice, Quot.sound]
#print axioms Ttc.traj_numlattice_le
-- [propext, Classical.choice, Quot.sound]
#print axioms Ttc.Box.boxProb                    -- the non-vacuity witness
-- [propext, Classical.choice, Quot.sound]
#print axioms Ttc.Box.nonempty_ttcProb
-- [propext, Classical.choice, Quot.sound]
```

```bash
# nothing (the `grep -v` drops the phrase "`sorry`-free" from two docstrings)
grep -rn "sorry\|admit\|native_decide\|sorryAx\|^axiom " Ttc.lean Ttc/ | grep -v '`sorry`'
```

See the README's [Verifying the claim](README.md#verifying-the-claim) for the
full-development axiom sweep.

**Checking §4's "which results does the headline actually reach" claim.** Paste
this into a file and `lake env lean` it; it walks the headline's transitive
constant set and reports membership.

```lean
import Ttc
open Lean in
run_cmd do
  let env ← Lean.getEnv
  let mut seen : Lean.NameSet := {}
  let mut todo := [`Ttc.TtcProb.volume_estimate]
  while !todo.isEmpty do
    let n := todo.head!; todo := todo.tail!
    if seen.contains n then continue
    seen := seen.insert n
    if let some ci := env.find? n then
      for c in ci.getUsedConstantsAsSet do todo := c :: todo
  for t in [`Ttc.Params.shell_factor_bound, `Ttc.Params.shell_factor_bound_deflated,
            `Ttc.Params.kappa_div_gamma_le, `Ttc.gamma_le_latticeScale_mul,
            `Ttc.prodKernel_claim_cl_b, `Ttc.Params.epsPrime_window,
            `Ttc.numlattice_failure_le, `Ttc.TtcProb.numlattice,
            `Ttc.TtcProb.numlattice_union, `Ttc.traj_numlattice_le,
            `Ttc.exists_epoch, `Ttc.TtcProb.thresh_pos,
            `Ttc.TtcProb.vol_le_total, `Ttc.trajLaw] do
    Lean.logInfo m!"{t} reached: {seen.contains t}"
```

**This reverses what this page said before, and the correction matters.** The
previous version reported `Ttc.traj_numlattice_le` as **`false`** — the coupling
built but not consumed by the capstone — and warned readers not to treat it as
load-bearing. That warning is now **wrong and withdrawn**. Running the walk above
from `Ttc.TtcProb.volume_estimate`, all four of

* `Ttc.TtcProb.numlattice`
* `Ttc.TtcProb.numlattice_union`
* `Ttc.traj_numlattice_le`
* `Ttc.trajLaw`

come back **`true`**. The coupling and the `lem:numlattice` bound proved over it
*are* on the headline's dependency path: `Model/Theorem` → `Coupling/NumLattice`
→ `Coupling/Transfer` → `Coupling/Run`. So "the coupling is
proved" and "the headline rests on it" are now the same statement.

This was checked by **running the transitive dependency walk over the compiled
environment**, not by reading the import graph — an import only says a file is
visible, not that any of its results is used. The import chain happens to agree
here, but the walk is what settles it, and it is the check to re-run after any
refactor.

`Ttc.numlattice_failure_le` also comes back **`true`**: it is what
`Ttc.TtcProb.numlattice` uses to turn the covering into `1 − δ`, so `Thresh` and
`ε'` are on the headline's path too.

# A machine-checked volume estimator for SMT(LRA) formulas

A Lean 4 + Mathlib formalization of **TTC**, the algorithm in
**_Efficient Volume Computation for SMT Formulas_** (preliminary version at KR 2025).

Given a formula `F` in linear real arithmetic and parameters `ε, δ ∈ (0, 1]`, TTC
estimates the volume of `F`'s solution set. It splits that set into polytopes, estimates
each polytope's volume with the Cousins–Vempala Gaussian-cooling algorithm (CV18), and
samples lattice points with Hit-and-Run, combining everything with a Poisson-thinning
counter.

This development proves the paper's two main theorems about the algorithm as printed:

* **Theorem 1 (accuracy):** the output is within a factor `1 ± ε` of the true volume with
  probability at least `1 − δ`;
* **Theorem 3 (running time):** the expected number of arithmetic operations is
  `Õ(m n⁵ ρ² r_max)`.

The proofs contain no `sorry` and use only Lean's three standard axioms:

```
#print axioms ttc.ttc_theorem1_volume_accuracy   ⇒  [propext, Classical.choice, Quot.sound]
#print axioms ttc.ttc_theorem3_expected_runtime  ⇒  [propext, Classical.choice, Quot.sound]
```

CV18 and Hit-and-Run are proved too, not assumed. Their guarantees come from the Lean
library [arlib-community](https://github.com/uddaloksarkar/arlib-community).


## The main theorems

Both theorems are in `ttc/Model/Theorem.lean`. Both are about `ttc`, the line-by-line
transcription of the paper's Algorithm 1 (`ttc/Model/Program.lean` and `ttc/Model/Run.lean`).

### Theorem 1: accuracy

```lean
theorem ttc_theorem1_volume_accuracy {n k : Nat}
    (hn : 21 ≤ n)
    (F : LRAFormula n k)
    (hbounded : Bornology.IsBounded (solutionSet F))
    (params : ApproxParams)
    (prep : TTCPreprocessor n k) :
    Pr[estimate ← ttc hn F hbounded params prep;
      (estimate : Real) ∈ Arlib.relErr params.epsilon (volume (solutionSet F)).toReal]
      ≥ 1 - params.delta
```

How to read it:

* `F` is an LRA formula with `n` real variables (and `k` Boolean ones);
* `params` packages `ε` and `δ` together with the proofs that `0 < ε ≤ 1` and `0 < δ ≤ 1`;
* `prep` is the preprocessing step (Boolean abstraction, DNF, normalization). It must
  return polytopes whose union is the solution set (see the limitations below);
* `relErr ε v` is the interval `[(1 − ε)·v, (1 + ε)·v]`.

So the theorem says: **with probability at least `1 − δ`, TTC's output lies in
`[(1 − ε)·vol(F), (1 + ε)·vol(F)]`.**

### Theorem 3: running time

```lean
theorem ttc_theorem3_expected_runtime ... :
    -- (1) counting operations does not change the algorithm
    (∀ S, MeasurableSet S →
      Pr[result ← ttcWithCost ...; result.1 ∈ S] = Pr[estimate ← ttc ...; estimate ∈ S]) ∧
    -- (2) the expected operation count is bounded
    Exp[result ← ttcWithCost ...; result.2] ≤
      preprocessingOperations + m * (30 n⁵ · r_max · ρ² · (⌈Thresh⌉ + 1) · polylogFactors / ε²)
```

`ttcWithCost` is the same algorithm with an operation counter attached. Part (1) says its
output has exactly the same distribution as `ttc`'s, so the bound in part (2) is about the
algorithm of Theorem 1. In part (2):

* `m` is the number of polytopes, `n` the dimension, and `r_max` the largest number of facets;
* `ρ = maxᵢ Rᵢ/γᵢ`, where `γᵢ` is the inradius of polytope `i` and `Rᵢ` the radius of a
  ball enclosing it;
* `polylogFactors` collects logarithmic factors in `n`, `m`, `ρ`, `R_max`, `1/γ_min`, `1/ε`
  and `1/δ`. Every constant is written out in `ttc/Model/Prelude.lean`.

So the expected cost is `Õ(m n⁵ ρ² r_max)`, as in the paper.


## What the theorems assume

A reader only needs to check these hypotheses:

* **`n ≥ 21`.** This comes from the formalized Hit-and-Run mixing theorem. The paper
  cites Lovász–Vempala without a dimension restriction.
* **The solution set is bounded.** Without this the volume can be infinite.
* **`0 < ε ≤ 1` and `0 < δ ≤ 1`.** These are fields of `ApproxParams`.

The conditions that CV18 and the sampler need (for example, a large enough inscribed
ball at precision `b`) are checked by the algorithm and proved to hold on every call.


## Limitations

Read these before citing the result.

* **Preprocessing is not formalized.** Boolean abstraction, DNF conversion and
  normalization (Theorem 2 of the paper) are an input `prep`. Its output type requires
  bounded, full-dimensional polytopes whose union equals the solution set almost
  everywhere, but Lean does not check how they are computed.
* **Most of the cost model is assumed.** Arithmetic is counted with one operation for
  each `·`, `+` and `≤` on real numbers. The membership test is a program written with
  these operations (`memberProg`, in the "Cost model" section of `ttc/Model/Prelude.lean`),
  and `ttc/Analysis/MembershipCost.lean` proves it is correct and costs exactly `2nr` in a
  polytope with `r` facets. CV18's oracle, the deletion pass and the sampler's rejection
  test all run this program, and the charged algorithm charges them what the program
  spends. The remaining charges are definitions in `ttc/Model/Prelude.lean`, not proved
  costs of a program:
  * one Hit-and-Run step: `2nr`, the same as a membership test;
  * uniform start point in the inscribed ball: `4n + 2`;
  * rounding a point to the lattice: `n`;
  * a fair coin, a Poisson or binomial draw, deleting or appending a copy, and a
    scalar update: `1` each.
* **Some costs are not counted.** The linear programs (`GetPrecision`, `BoundingRadius`)
  and preprocessing are not charged; preprocessing enters only as the number
  `preprocessingOperations`. CV18's work besides membership queries is charged by a
  single factor. Rewriting each polytope's offsets once for CV18's normalized body and
  for the `10^b`-scaled body (`O(nr)` per polytope) is not charged.
* **Exact real arithmetic.** The algorithm works over the real numbers. Rounding error in
  floating point is not modelled.
* **The `ε` dependence is looser than the paper's.** Lean's bound multiplies the
  volume and sampling costs, giving `1/ε⁴`. The `n⁵ ρ² r_max m` shape matches.


## Paper → Lean

| Paper | Lean | Where |
|---|---|---|
| Algorithm 1 (`ttc`) | `ttcPseudocode`, `ttc` | `Model/Program.lean`, `Model/Run.lean` |
| `GetPrecision`, `MaxInscribedBall` | `GetPrecision`, `HalfspacePresentation.MaxInscribedBall` | `Model/Run.lean`, `Model/Prelude.lean` |
| `BoundingRadius` | `PolytopeData.BoundingRadius` | `Model/Run.lean` |
| `VolED` (Corollary `cor:vol`) | `communityCV18VolumeLaw` | `Model/Run.lean` |
| `GenerateSamples` (Corollary `cor:linf`) | `normalizedHitAndRunPointLaw` | `Model/Run.lean` |
| Proposition `prop:bounding-radius`, `R₀ ≤ 2√n R` | `PolytopeData.boundingRadius_le` | `Analysis/BoundingRadius.lean` |
| Lemma `lem:nonconv` (lattice points vs. volume) | `L2LatticeUnion.lean` | `Analysis/` |
| Theorem 1 (`thm:volumettc`) | `ttc_theorem1_volume_accuracy` | `Model/Theorem.lean` |
| Theorem 3 (`thm:runtime`) | `ttc_theorem3_expected_runtime` | `Model/Theorem.lean` |

Small differences from the paper:

* The Hit-and-Run walk constant is `C = 2⁶⁸`. This is what the formalized mixing bound
  (`2⁶⁴ n² D² log(8M/ν²)`) needs.
* In Lemma `lem:nonconv`, the bound `κ/γ ≤ η/(32mn)` should read `η/(26mn)`. The lemma
  still holds.
* The proofs use an equivalent version of the algorithm that starts from `p = 1` instead
  of `p = Thresh`. `Analysis/TTCSimulation.lean` proves the two have the same output.


## The audit surface: `Model/`

To trust the theorems you need to read only `ttc/Model/`. It contains definitions and
statements, and no proofs.

1. **`Prelude.lean`**: the vocabulary. LRA formulas, polytopes (`PolytopeData`), the
   Chebyshev-centre LP, the parameters `ε' = ε/12`, `δ' = δ/(4m)` and `Thresh`, and the
   cost model.
2. **`Program.lean`**: Algorithm 1's control flow, with its subroutines left as slots.
   Starting from `p ← Thresh`, `X ← ∅`, it processes each polytope in turn: remove the
   points of `X` inside it, the rate check `k ← ⌈log₂(tp/Thresh)⌉`, the Poisson draw,
   the halving loop, sampling, and append. It ends by returning `|X| / (p·10^{bn})`.
   It also contains the same algorithm with operation counts.
3. **`Run.lean`**: the concrete subroutines (`GetPrecision`, `BoundingRadius`, CV18 and
   the Hit-and-Run sampler), and `ttc` itself.
4. **`Theorem.lean`**: the two theorems.

`ttc/Meta/ModelClosure.lean` checks on every build that everything the theorems mention
is defined in `Model/`, so nothing hidden in `Analysis/` can change what they say.


## How the proof goes

**Theorem 1.**

1. With the volume estimates fixed, the points kept at each rate level form a Poisson
   process whose mean is the number of lattice points times that rate.
2. A Chernoff bound shows the final count is accurate except with probability `δ/6`, and
   the chance of ending at a bad level is at most another `δ/6`.
3. CV18 fails with probability at most `δ/4` in total over all `m` calls.
4. Lemma `lem:nonconv` turns a lattice-point estimate into a volume estimate.

**Theorem 3.** Per polytope, the cost is: CV18's query count times `n·r`, plus
`⌈Thresh⌉` samples times the walk length `T` times `n·r`, plus thinning and deletion.
`T` is bounded by `n⁴ρ²` up to logarithms, using `R₀ ≤ 2√n R`. The CV18 query bound
comes from arlib-community.


## How to verify

1. Build:

   ```sh
   cd lean
   lake exe cache get    # download Mathlib's compiled files; skipping this takes hours
   lake build
   ```

   The toolchain is `leanprover/lean4:v4.35.0`, with Mathlib `v4.35.0`.
   arlib and arlib-community are pinned in `lakefile.toml`.

2. Check that there are no `sorry`s:

   ```sh
   lake build 2>&1 | grep -i "declaration uses 'sorry'"    # should print nothing
   ```

3. Check the axioms. The two `#print axioms` lines at the end of
   `ttc/Model/Theorem.lean` print them during the build. Both should show
   `[propext, Classical.choice, Quot.sound]`.

4. Read `ttc/Model/` in the order above, side by side with the paper.


## Layout

```
lean/
├── ttc.lean            root module
├── ttc/
│   ├── Model/          what is claimed: definitions, the algorithm, the theorems
│   ├── Analysis/       the proofs
│   └── Meta/           the check that the theorems are stated in Model/ terms
├── lakefile.toml       dependencies (Mathlib, arlib, arlib-community)
└── scripts/            list of the headline theorems
```

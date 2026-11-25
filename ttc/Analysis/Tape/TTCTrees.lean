/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import ttc.Analysis.Tape.Primitives

/-!
# Algorithm `ttc` as trees

Each procedure of Algorithm `ttc` (`Model/SealedProgram.lean`) written as a tree, following
its text, and the statement that the two agree (`agree_*`).  CV18 is a parameter here: the
procedures that call it take its tree `cv18T` and the statement that it agrees with the
program's `cv18` (`Analysis/Tape/CV18Trees.lean`).
-/

set_option autoImplicit false
set_option linter.unusedVariables false

noncomputable section

namespace ttc.Tape

open Arlib.Computation (Num Charged)
open ttc.Model.Operations
open ttc.Program
open ttc.Tape.Tree

variable {d : ℕ} {α β γ : Type}

/-! ## Agreement, step by step -/

theorem Agree.bindT {X : M d α} {p : Tree d α} {F : α → M d β} {f : α → Tree d β}
    (hX : Agree X (interp p)) (hF : ∀ a, Agree (F a) (interp (f a))) :
    Agree (X >>= F) (interp (p.bind f)) := by
  rw [interp_bind]
  exact Agree.bind hX hF

theorem agree_run (c : Prog α) : Agree (run c : M d α) (interp (compute c)) :=
  Agree.of_eq (interp_compute c).symm

theorem agree_pure (a : α) : Agree (Pure.pure a : M d α) (interp (Tree.pure a)) :=
  Agree.refl _

theorem agree_fail : Agree (failure : M d α) (interp (Tree.fail : Tree d α)) :=
  Agree.refl _

theorem agree_coin : Agree (Program.coin : M d Bool) (interp coinT) :=
  Agree.of_eq interp_coinT.symm

theorem agree_unit : Agree (Program.unit : M d (Num ℝ)) (interp unitT) :=
  Agree.of_eq interp_unitT.symm

theorem agree_gaussian : Agree (Program.gaussian : M d (NumPoint d)) (interp gaussianT) :=
  Agree.of_eq interp_gaussianT.symm

theorem agree_poisson (r : Num ℝ) : Agree (Program.poisson r : M d (Num ℕ)) (interp (poissonT r)) :=
  Agree.of_eq (interp_poissonT r).symm

theorem agree_binom (N : Num ℕ) :
    Agree (withOracle (drawBinomialHalf N) : M d (Num ℕ)) (interp (binomT N)) :=
  Agree.of_eq (interp_binomT N).symm

theorem agree_ite (c : Bool) {X Y : M d α} {p q : Tree d α} (hX : Agree X (interp p))
    (hY : Agree Y (interp q)) : Agree (if c then X else Y) (interp (if c then p else q)) := by
  cases c
  · exact hY
  · exact hX

theorem agree_loop (count : Num ℕ) {bodyM : β → M d (β ⊕ γ)} {body : β → Tree d (β ⊕ γ)}
    (h : ∀ b, Agree (bodyM b) (interp (body b))) (init : β) :
    Agree (loopUntil count bodyM init) (interp (loopTree count body init)) :=
  loopUntil_agree count bodyM body h init

/-- A fold over a list, step by step. -/
theorem agree_foldlM {ι : Type} {f : β → ι → M d β} {g : β → ι → Tree d β}
    (h : ∀ b x, Agree (f b x) (interp (g b x))) :
    ∀ (l : List ι) (b : β), Agree (l.foldlM f b) (interp (l.foldlM g b))
  | [], b => agree_pure b
  | x :: l, b => by
      simp only [List.foldlM_cons]
      exact Agree.bindT (h b x) fun b' => agree_foldlM h l b'

/-! ## Hit-and-Run -/

/-- One lazy Hit-and-Run step, as a tree. -/
def hitAndRunStepT (r : ℕ) (a : Fin r → NumPoint d) (β' : Fin r → Num ℝ) (x : NumPoint d) :
    Tree d (NumPoint d) :=
  coinT.bind fun stay =>
    if stay then .pure x else
      gaussianT.bind fun g =>
        (compute (normalize g)).bind fun θ =>
          (compute (chord r a β' x θ)).bind fun ends =>
            match ends with
            | (some lo, some hi) =>
                (compute (A.lt lo hi)).bind fun ok =>
                  if ok then
                    unitT.bind fun u =>
                      compute (do
                        let width ← A.sub hi lo
                        let shift ← A.mul u width
                        let t ← A.add lo shift
                        A.forEach fun i => do
                          let step ← A.mul t (θ i)
                          A.add (x i) step)
                  else .pure x
            | _ => .pure x

theorem agree_hitAndRunStep (r : ℕ) (a : Fin r → NumPoint d) (β' : Fin r → Num ℝ)
    (x : NumPoint d) :
    Agree (hitAndRunStep r a β' x) (interp (hitAndRunStepT r a β' x)) := by
  refine Agree.bindT agree_coin fun stay => ?_
  cases stay
  · refine Agree.bindT agree_gaussian fun g => ?_
    refine Agree.bindT (agree_run _) fun θ => ?_
    refine Agree.bindT (agree_run _) fun ends => ?_
    rcases ends with ⟨_ | lo, _ | hi⟩
    · exact agree_pure x
    · exact agree_pure x
    · exact agree_pure x
    · refine Agree.bindT (agree_run _) fun ok => ?_
      refine agree_ite ok ?_ (agree_pure x)
      exact Agree.bindT agree_unit fun u => agree_run _
  · exact agree_pure x

/-- `steps` Hit-and-Run steps, as a tree. -/
def hitAndRunWalkT (r : ℕ) (a : Fin r → NumPoint d) (β' : Fin r → Num ℝ) (steps : Num ℕ)
    (x : NumPoint d) : Tree d (NumPoint d) :=
  (loopTree (γ := Empty) steps (fun y => (hitAndRunStepT r a β' y).bind fun y' =>
      .pure (.inl y')) x).bind fun res =>
    .pure (match res with
      | .inl y => y
      | .inr e => e.elim)

theorem agree_hitAndRunWalk (r : ℕ) (a : Fin r → NumPoint d) (β' : Fin r → Num ℝ)
    (steps : Num ℕ) (x : NumPoint d) :
    Agree (hitAndRunWalk r a β' steps x) (interp (hitAndRunWalkT r a β' steps x)) :=
  Agree.bindT
    (agree_loop steps (fun y => Agree.bindT (agree_hitAndRunStep r a β' y) fun y' =>
      agree_pure _) x)
    fun res => agree_pure _

/-! ## Rounding and sampling -/

/-- The rounding, coordinate by coordinate, as a tree. -/
def roundCoordsT (one : Num ℤ) : (k : ℕ) → (Fin k → Num ℝ) → Tree d (Fin k → Num ℤ)
  | 0, _ => .pure Fin.elim0
  | k + 1, q =>
      unitT.bind fun v =>
        (compute (do
          let fl ← floor (q 0)
          let flR ← intCast fl
          let frac ← A.sub (q 0) flR
          let up ← A.lt v frac
          if up then A.add fl one else A.pure fl)).bind fun z =>
          (roundCoordsT one k (Fin.tail q)).bind fun rest => .pure (Fin.cons z rest)

theorem agree_roundCoords (one : Num ℤ) :
    ∀ (k : ℕ) (q : Fin k → Num ℝ),
      Agree (roundCoords (d := d) one k q) (interp (roundCoordsT one k q))
  | 0, _ => agree_pure _
  | k + 1, q =>
      Agree.bindT agree_unit fun v => Agree.bindT (agree_run _) fun z =>
        Agree.bindT (agree_roundCoords one k (Fin.tail q)) fun rest => agree_pure _

/-- KV97 rounding, as a tree. -/
def roundPointT (p : NumPoint d) : Tree d (Fin d → Num ℤ) :=
  (compute (A.lit (1 : ℤ))).bind fun one => roundCoordsT one d p

theorem agree_roundPoint (p : NumPoint d) : Agree (Program.roundPoint p) (interp (roundPointT p)) :=
  Agree.bindT (agree_run _) fun one => agree_roundCoords one d p

/-- One attempt at a sample, as a tree. -/
def sampleTryT (L : Loaded d) (W : WalkConstants d L.facets) (scaled : Fin L.facets → Num ℝ)
    (dimN : Num ℕ) : Tree d (Option (Fin d → Num ℤ)) :=
  gaussianT.bind fun g =>
    unitT.bind fun u =>
      (compute (A.ballStart dimN g u)).bind fun y₀ =>
        (hitAndRunWalkT L.facets L.normal W.offsets W.steps y₀).bind fun y =>
          (compute (A.forEach fun i => do
              let s ← A.mul W.scaledInradius (y i)
              A.add s (W.scaledIncenter i))).bind fun p =>
            (roundPointT p).bind fun z =>
              (compute (latticeMember L scaled z)).bind fun ok =>
                .pure (if ok then some z else none)

theorem agree_sampleTry (L : Loaded d) (W : WalkConstants d L.facets)
    (scaled : Fin L.facets → Num ℝ) (dimN : Num ℕ) :
    Agree (sampleTry L W scaled dimN) (interp (sampleTryT L W scaled dimN)) :=
  Agree.bindT agree_gaussian fun g => Agree.bindT agree_unit fun u =>
    Agree.bindT (agree_run _) fun y₀ =>
      Agree.bindT (agree_hitAndRunWalk _ _ _ _ y₀) fun y =>
        Agree.bindT (agree_run _) fun p => Agree.bindT (agree_roundPoint p) fun z =>
          Agree.bindT (agree_run _) fun ok => agree_pure _

/-- Attempts until one is accepted, with `fuel` rounds, as a tree. -/
def sampleUntilAcceptedT (L : Loaded d) (W : WalkConstants d L.facets)
    (scaled : Fin L.facets → Num ℝ) (dimN : Num ℕ) : ℕ → Tree d (Fin d → Num ℤ)
  | 0 => .fail
  | fuel + 1 =>
      (sampleTryT L W scaled dimN).bind fun r =>
        match r with
        | some z => .pure z
        | none => sampleUntilAcceptedT L W scaled dimN fuel

theorem agree_sampleUntilAccepted (L : Loaded d) (W : WalkConstants d L.facets)
    (scaled : Fin L.facets → Num ℝ) (dimN : Num ℕ) :
    ∀ fuel, Agree (sampleUntilAccepted L W scaled dimN fuel)
      (interp (sampleUntilAcceptedT L W scaled dimN fuel))
  | 0 => agree_fail
  | fuel + 1 => by
      refine Agree.bindT (agree_sampleTry L W scaled dimN) fun r => ?_
      rcases r with _ | z
      · exact agree_sampleUntilAccepted L W scaled dimN fuel
      · exact agree_pure z

/-! ## Thinning and the halving loop -/

/-- Keep the copies for which `keep` says so, counting them, as a tree. -/
def filterCopiesT (keep : (Fin d → Num ℤ) → Tree d Bool) (X : List (Fin d → Num ℤ)) :
    Tree d (List (Fin d → Num ℤ) × Num ℕ) :=
  (compute (A.lit (0 : ℕ))).bind fun zero =>
    (compute (A.lit (1 : ℕ))).bind fun one =>
      X.foldlM (fun (acc : List (Fin d → Num ℤ) × Num ℕ) x =>
        (compute (A.cell x)).bind fun x =>
          (keep x).bind fun k =>
            if k then
              (compute (A.push acc.1 x)).bind fun ys =>
                (compute (A.add acc.2 one)).bind fun c => .pure (ys, c)
            else .pure acc) ([], zero)

theorem agree_filterCopies {keepM : (Fin d → Num ℤ) → M d Bool}
    {keep : (Fin d → Num ℤ) → Tree d Bool} (h : ∀ x, Agree (keepM x) (interp (keep x)))
    (X : List (Fin d → Num ℤ)) :
    Agree (filterCopies keepM X) (interp (filterCopiesT keep X)) :=
  Agree.bindT (agree_run _) fun zero => Agree.bindT (agree_run _) fun one =>
    agree_foldlM (fun acc x => Agree.bindT (agree_run _) fun x' =>
      Agree.bindT (h x') fun k => agree_ite k
        (Agree.bindT (agree_run _) fun ys => Agree.bindT (agree_run _) fun c => agree_pure _)
        (agree_pure _)) X _

/-- The halving loop, with `fuel` rounds, as a tree. -/
def halveT (K : Params) : ℕ → Num ℝ → List (Fin d → Num ℤ) → Num ℕ → Num ℕ →
    Tree d (Num ℝ × List (Fin d → Num ℤ) × Num ℕ × Num ℕ)
  | 0, _, _, _, _ => .fail
  | f + 1, p, X, size, N =>
      (compute (do
        let total ← A.add size N
        let totalR ← A.cast total
        A.le totalR K.thresh)).bind fun stop =>
        if stop then .pure (p, X, size, N) else
          (filterCopiesT (fun _ => coinT) X).bind fun r =>
            (binomT N).bind fun N' =>
              (compute (A.divLit p 2)).bind fun p' =>
                halveT K f p' r.1 r.2 N'

theorem agree_halve (K : Params) :
    ∀ (f : ℕ) (p : Num ℝ) (X : List (Fin d → Num ℤ)) (size N : Num ℕ),
      Agree (halve K f p X size N) (interp (halveT K f p X size N))
  | 0, _, _, _, _ => agree_fail
  | f + 1, p, X, size, N => by
      refine Agree.bindT (agree_run _) fun stop => ?_
      refine agree_ite stop (agree_pure _) ?_
      refine Agree.bindT (agree_filterCopies (fun _ => agree_coin) X) fun r => ?_
      obtain ⟨X', size'⟩ := r
      exact Agree.bindT (agree_binom N) fun N' => Agree.bindT (agree_run _) fun p' =>
        agree_halve K f p' X' size' N'

/-! ## One component, and the algorithm -/

/-- CV18 as a tree, as the procedures below take it. -/
abbrev CV18Tree (d : ℕ) := (NumPoint d → Prog Bool) → Num ℝ → Num ℝ → Num ℝ → Tree d (Num ℝ)

/-- `cv18T` stands for the program's `cv18`. -/
def CV18Agrees (cv18T : CV18Tree d) : Prop :=
  ∀ member eps roundness p, Agree (cv18 d member eps roundness p)
    (interp (cv18T member eps roundness p))

/-- One iteration of the `for` loop, as a tree. -/
def stepT (cv18T : CV18Tree d) (fuel : ℕ) (K : Params) (L : Loaded d) (s : State d) :
    Tree d (State d) :=
  (compute (cv18Offsets L)).bind fun off' =>
  (compute (do
    let epsC ← A.divLit K.epsPrime 2
    let pC ← A.divLit K.deltaPrime 2
    let rg ← A.div L.boundingRadius L.inradius
    let m ← A.litMax 1 rg
    let m2 ← A.pow m 2
    let roundness ← A.div m2 K.dim
    A.pure (epsC, pC, roundness))).bind fun x =>
  match x with
  | (epsC, pC, roundness) =>
  (cv18T (allFacets L.facets L.normal off') epsC roundness pC).bind fun v =>
  (compute (do
    let zero ← A.lit (0 : ℝ)
    let v' ← A.max zero v
    let γn ← powHeld L.inradius K.dimN
    let vol ← A.mul γn v'
    A.mul K.scaleN vol)).bind fun t =>
  (compute (scaledOffsets L K.scale)).bind fun scaled =>
  (filterCopiesT (fun x => (compute (latticeMember L scaled x)).bind fun inside =>
      .pure (!inside)) s.X).bind fun r =>
  match r with
  | (X, size) =>
  (compute (A.mul t s.p)).bind fun tp =>
  (compute (A.le K.thresh tp)).bind fun big =>
  (if big then
      (compute (do
        let ratio ← A.div tp K.thresh
        let lr ← A.log ratio
        let two ← A.lit (2 : ℝ)
        let l2 ← A.log two
        let kR ← A.div lr l2
        let k ← A.ceil kR
        let twoK ← powHeld two k
        let p' ← A.div s.p twoK
        let one ← A.lit (1 : ℝ)
        let keepProb ← A.div one twoK
        A.pure (p', keepProb))).bind fun y =>
      match y with
      | (p', keepProb) =>
      (filterCopiesT (fun _ => unitT.bind fun u => compute (A.lt u keepProb)) X).bind fun r' =>
      match r' with
      | (X', size') => .pure (p', X', size')
    else .pure (s.p, X, size)).bind fun q =>
  match q with
  | (p, X, size) =>
  (compute (A.mul t p)).bind fun rate =>
  (poissonT rate).bind fun N =>
  (halveT K fuel p X size N).bind fun h =>
  match h with
  | (p, X, size, N) =>
  (compute (walkConstantsProg L K.scale K.epsPrime K.dim)).bind fun W =>
  (loopTree (γ := Empty) N (fun (acc : List (Fin d → Num ℤ) × Num ℕ) =>
      (sampleUntilAcceptedT L W scaled K.dimN fuel).bind fun z =>
      (compute (A.push acc.1 z)).bind fun ys =>
      (compute (do
        let one ← A.lit (1 : ℕ)
        A.add acc.2 one)).bind fun c =>
      .pure (.inl (ys, c))) (X, size)).bind fun res =>
  let (X, size) := match res with
    | .inl r => r
    | .inr e => e.elim
  .pure ⟨p, X, size⟩

theorem agree_step {cv18T : CV18Tree d} (hcv : CV18Agrees cv18T) (fuel : ℕ) (K : Params)
    (L : Loaded d) (s : State d) :
    Agree (Program.step fuel K L s) (interp (stepT cv18T fuel K L s)) := by
  refine Agree.bindT (agree_run _) fun off' => ?_
  refine Agree.bindT (agree_run _) fun x => ?_
  obtain ⟨epsC, pC, roundness⟩ := x
  refine Agree.bindT (hcv _ _ _ _) fun v => ?_
  refine Agree.bindT (agree_run _) fun t => ?_
  refine Agree.bindT (agree_run _) fun scaled => ?_
  refine Agree.bindT (agree_filterCopies (fun x => Agree.bindT (agree_run _) fun inside =>
    agree_pure _) s.X) fun r => ?_
  obtain ⟨X, size⟩ := r
  refine Agree.bindT (agree_run _) fun tp => ?_
  refine Agree.bindT (agree_run _) fun big => ?_
  refine Agree.bindT (agree_ite big ?_ (agree_pure _)) fun q => ?_
  · refine Agree.bindT (agree_run _) fun y => ?_
    obtain ⟨p', keepProb⟩ := y
    refine Agree.bindT (agree_filterCopies (fun _ => Agree.bindT agree_unit fun u =>
      agree_run _) X) fun r' => ?_
    obtain ⟨X', size'⟩ := r'
    exact agree_pure _
  obtain ⟨p, X, size⟩ := q
  refine Agree.bindT (agree_run _) fun rate => ?_
  refine Agree.bindT (agree_poisson rate) fun N => ?_
  refine Agree.bindT (agree_halve K fuel p X size N) fun h => ?_
  obtain ⟨p, X, size, N⟩ := h
  refine Agree.bindT (agree_run _) fun W => ?_
  refine Agree.bindT (agree_loop N (fun acc =>
    Agree.bindT (agree_sampleUntilAccepted L W scaled K.dimN fuel) fun z =>
    Agree.bindT (agree_run _) fun ys => Agree.bindT (agree_run _) fun c => agree_pure _) _)
    fun res => ?_
  exact agree_pure _

/-- The parameters of the run, computed (as in `estimator`). -/
def paramsProg {d : ℕ} (cs : List (ComponentInput d)) (Ls : List (Loaded d)) (eps delta : ℝ) :
    Prog Params := do
  let dimN ← A.lit d
  let dim ← A.cast dimN
  let zero ← A.lit (0 : ℕ)
  let one ← A.lit (1 : ℕ)
  let (mN, rTot) ← cs.foldlM (fun (acc : Num ℕ × Num ℕ) c => do
      let m' ← A.add acc.1 one
      let r ← A.lit c.facetCount
      let t' ← A.add acc.2 r
      A.pure (m', t')) (zero, zero)
  let m ← A.cast mN
  let rTotR ← A.cast rTot
  let eps ← A.lit eps
  let delta ← A.lit delta
  let epsPrime ← A.divLit eps 12
  let m4 ← A.mulLit 4 m
  let deltaPrime ← A.div delta m4
  let a1 ← A.litDiv 24 delta
  let a2 ← A.log a1
  let a3 ← A.mulLit 24 a2
  let one ← A.lit (1 : ℝ)
  let b1 ← A.sub one epsPrime
  let b2 ← A.pow epsPrime 2
  let b3 ← A.mul b1 b2
  let first ← A.div a3 b3
  let c1 ← A.litDiv 6 delta
  let c2 ← A.log c1
  let c3 ← A.log m
  let c4 ← A.add c2 c3
  let second ← A.mulLit 15 c4
  let thresh ← A.max first second
  let eta ← A.divLit eps 96
  let required ← latticeRadiusProg m dim rTotR eta
  let b ← getPrecision required Ls
  let scale ← pow10 b
  let bn ← A.mul b dimN
  let scaleN ← pow10 bn
  A.pure (⟨epsPrime, deltaPrime, thresh, dim, dimN, scale, scaleN⟩ : Params)

/-- **Algorithm `ttc`**, as a tree. -/
def estimatorT (cv18T : CV18Tree d) (fuel : ℕ) (cs : List (ComponentInput d)) (eps delta : ℝ) :
    Tree d (Num ℝ) :=
  match cs with
  | [] => compute (A.lit (0 : ℝ))
  | _ :: _ =>
    (compute (cs.mapM load)).bind fun Ls =>
    (compute (paramsProg cs Ls eps delta)).bind fun K =>
    (compute (A.lit (0 : ℕ))).bind fun zero =>
    (Ls.foldlM (fun s L => stepT cv18T fuel K L s) (⟨K.thresh, [], zero⟩ : State d)).bind
      fun final =>
    compute (do
      let size ← A.cast final.size
      let den ← A.mul final.p K.scaleN
      A.div size den)

theorem agree_estimator {cv18T : CV18Tree d} (hcv : CV18Agrees cv18T) (fuel : ℕ)
    (cs : List (ComponentInput d)) (eps delta : ℝ) :
    Agree (estimator fuel cs eps delta) (interp (estimatorT cv18T fuel cs eps delta)) := by
  cases cs with
  | nil => exact agree_run _
  | cons c cs =>
      refine Agree.bindT (agree_run _) fun Ls => ?_
      refine Agree.bindT (agree_run _) fun K => ?_
      refine Agree.bindT (agree_run _) fun zero => ?_
      refine Agree.bindT (agree_foldlM (fun s L => agree_step hcv fuel K L s) Ls _)
        fun final => ?_
      exact agree_run _

end ttc.Tape

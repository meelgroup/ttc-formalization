/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Lean

/-!
# `#sealedProgram`: the program does no free computation

Machine-checks that a program computes only through charged operations.  Starting from
the program's body, it walks every definition of this project and of arlib-community the
program uses and fails
if one of them

* reads a sealed value (`Num.get`, `NumPoint.view`, `Counted.value`, `Charged.val`);
* builds a node of the program tree by hand, outside the primitives that charge for it;
* chooses classically (`Classical.choose`, `sInf`, …) or branches on a real comparison; or
* does real arithmetic itself (`+ − · /`, powers, `√`, `exp`, `log`, `max`, `min` at `ℝ`)
  on anything but closed constants (folding literals such as `1 / 2` is not computation).

The **primitives** are the sanctioned boundary and are not looked into: the oracle call
(`isMember`), the draws (`drawPoint`, `drawReal`), running charged arithmetic (`compute`),
the loop and the query cap over a held count (each charging one `NumOp.loop`), and
`report`, where the answer leaves the sealed world.  arlib's own operations are not looked
into either: they are where the charging happens.

Probability laws and proofs are not computation, so definitions whose type is a measure,
a `PMF`, or a proposition are skipped.

This is tooling, outside the surface it checks.
-/

open Lean Elab Command Meta

namespace ttc.Meta

private def cv18 (s : String) : Name := (`ttc.ChargedCV18).append s.toName

/-- The sanctioned primitives: neither scanned nor walked into. -/
private def primitives : List Name :=
  [cv18 "isMember", cv18 "drawPoint", cv18 "drawReal", cv18 "compute", cv18 "loopUntil",
   cv18 "report", cv18 "ChargedProgram.loopRounds",
   cv18 "ChargedProgram.withHeldQueryCap", cv18 "ChargedProgram.withQueryCap",
   cv18 "ChargedProgram.bind", cv18 "Counted.isMember", cv18 "Counted.pick",
   -- The former arlib fork's five real-RAM primitives now live in TTC's
   -- trusted Operations module. Each opens and reseals a register for one charge.
   `Arlib.Computation.Num.cast, `Arlib.Computation.Num.sqrt, `Arlib.Computation.Num.exp,
   `Arlib.Computation.Num.log, `Arlib.Computation.Num.root]

/-- Constants a program may not reach outside the primitives. -/
private def forbidden : List Name :=
  [`Arlib.Computation.Num.get, `Arlib.Computation.Charged.val,
   cv18 "NumPoint.view", cv18 "Counted.value",
   cv18 "ChargedProgram.query", cv18 "ChargedProgram.randomNat",
   cv18 "ChargedProgram.randomPoint", cv18 "ChargedProgram.randomReal",
   cv18 "ChargedProgram.tick",
   `Classical.choose, `Classical.epsilon, `Classical.indefiniteDescription,
   `InfSet.sInf, `SupSet.sSup, `Nat.find]

/-- Operators that are free arithmetic when their first (type) argument is `ℝ`. -/
private def realOps : List Name :=
  [`HAdd.hAdd, `HSub.hSub, `HMul.hMul, `HDiv.hDiv, `HPow.hPow, `HSMul.hSMul,
   `Neg.neg, `Inv.inv, `Max.max, `Min.min]

/-- Real functions that are free computation when applied. -/
private def realFns : List Name := [`Real.sqrt, `Real.log, `Real.exp, `Real.rpow]

/-- Decisions of real comparisons.  Passed to an arlib comparison they are sanctioned (the
comparison is charged); driving an `if` or a `decide` they are a free comparison. -/
private def realDecisions : List Name :=
  [`Real.decidableLT, `Real.decidableLE, `Real.decidableEq]

/-- Branching constructs and the position of their `Decidable` argument. -/
private def branchers : List (Name × Nat) := [(`ite, 2), (`dite, 2), (`Decidable.decide, 1)]

/-- Is `e` the type `ℝ`? -/
private def isReal (e : Expr) : Bool := e.isConstOf `Real

/-- The free computations in `e`, as readable strings. -/
private partial def scan (e : Expr) : StateM (Array String) Unit := do
  match e with
  | .app .. =>
      let fn := e.getAppFn
      let args := e.getAppArgs
      -- arithmetic on closed constants is literal folding; it is free computation only
      -- when it depends on a program value or a parameter (a bound variable)
      let live := e.hasLooseBVars
      if let .const c _ := fn then
        if forbidden.contains c then modify (·.push s!"{c}")
        if live && realOps.contains c && args.size > 0 && isReal args[0]! then
          modify (·.push s!"{c} at ℝ")
        if live && realFns.contains c then modify (·.push s!"{c}")
        if let some (_, i) := branchers.find? (·.1 == c) then
          if h : i < args.size then
            if let .const d _ := args[i].getAppFn then
              if realDecisions.contains d then modify (·.push s!"{c} on {d}")
      else scan fn
      for a in args do scan a
  | .const c _ => if forbidden.contains c then modify (·.push s!"{c}")
  | .lam _ t b _ | .forallE _ t b _ => scan t; scan b
  | .letE _ t v b _ => scan t; scan v; scan b
  | .mdata _ b => scan b
  | .proj _ _ b => scan b
  | _ => pure ()

/-- Is `c` a law, a proof, or a proposition — not computation? -/
private def isSpecOnly (ci : ConstantInfo) : MetaM Bool := do
  if ci matches .thmInfo _ then return true
  forallTelescopeReducing ci.type fun _ body => do
    if ← isProp body then return true
    if body.isSort then return true
    let fn := body.getAppFn
    return fn.isConstOf `MeasureTheory.Measure || fn.isConstOf `PMF ||
      fn.isConstOf `MeasureTheory.IsProbabilityMeasure

/-- Walk the package definitions reachable from `seed`, collecting free computations. -/
private partial def walk (seed : Name) : MetaM (Array (Name × String)) := do
  let env ← getEnv
  let rec go (todo : List Name) (seen : NameSet) (acc : Array (Name × String)) :
      MetaM (Array (Name × String)) := do
    match todo with
    | [] => return acc
    | c :: rest =>
      if seen.contains c || primitives.contains c then return ← go rest seen acc
      let seen := seen.insert c
      let inPackage := match env.getModuleIdxFor? c with
        | some idx =>
            let m := (env.allImportedModuleNames[idx.toNat]?).getD `«unknown»
            (`ttc).isPrefixOf m || (`ArlibCommunity).isPrefixOf m
        | none => true
      let some ci := env.find? c | return ← go rest seen acc
      if !inPackage || (← isSpecOnly ci) then return ← go rest seen acc
      let some v := ci.value? | return ← go rest seen acc
      let ((), found) := (scan v).run #[]
      let acc := acc ++ found.map (c, ·)
      go (v.getUsedConstants.toList ++ rest) seen acc
  go [seed] {} #[]

/-- **Check that a program does no free computation.**  See the module docstring. -/
elab "#sealedProgram " id:ident : command => do
  let env ← getEnv
  for c in primitives ++ forbidden ++ realFns ++ realDecisions do
    unless env.contains c do throwError m!"#sealedProgram: unknown constant {c}"
  let seed ← liftCoreM <| realizeGlobalConstNoOverload id
  let bad ← liftTermElabM <| walk seed
  if bad.isEmpty then
    logInfo m!"OK — {seed} computes only through charged operations"
  else
    let lines := bad.toList.map fun (c, what) => m!"\n  {c}: {what}"
    throwError m!"free computation in {seed}:{MessageData.joinSep lines ""}"

end ttc.Meta

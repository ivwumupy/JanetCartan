module

public meta import Lean

/-!
# Exact caches for the original extension and seed output clauses

These two commands apply the already retained original callback to arbitrary
parameters and cache a fixed number of its literal `Exists`/`And` clauses.
The two large left clauses (seed result and leading continuation) receive
exact proposition names as well. All generated declarations are ordinary
kernel-checked definitions/theorems; none is an axiom or assumed conclusion.
-/

public meta section
namespace JanetCartan.ContinuumInverse.InitializedCappedHistory.ReferenceBoundary.Generator
open Lean Meta Elab Command

private def addDefinition (name : Name) (params : Array Expr)
    (type value : Expr) : MetaM Expr := do
  addDecl (.defnDecl {
    name, levelParams := [], type := ← mkForallFVars params type,
    value := ← mkLambdaFVars params value,
    hints := .abbrev, safety := .safe }) (forceExpose := true)
  return mkAppN (mkConst name) params

private def addTheorem (name : Name) (params : Array Expr)
    (type value : Expr) : MetaM Expr := do
  addDecl (.thmDecl {
    name, levelParams := [], type := ← mkForallFVars params type,
    value := ← mkLambdaFVars params value }) (forceExpose := true)
  return mkAppN (mkConst name) params

private partial def cacheFixedPrefix (ns : Name) (params : Array Expr)
    (type : Expr) (index last : Nat) : MetaM Expr := do
  if index == last then
    return ← addDefinition (ns.str "Continuation") params (mkSort 0) type
  let type ← whnf type
  let value ← if type.isAppOfArity ``Exists 2 then
    match type.appArg! with
    | .lam name domain body _ =>
      withLocalDeclD name domain fun witness => do
        let tail ← cacheFixedPrefix ns (params.push witness) (body.instantiate1 witness)
          (index + 1) last
        mkAppM ``Exists #[← mkLambdaFVars #[witness] tail]
    | _ => throwError "prescribed reference boundary: expected existential predicate"
  else if type.isAppOfArity ``And 2 then do
    let left ← addDefinition (ns.str s!"FactType{index}") params (mkSort 0) type.appFn!.appArg!
    let tail ← cacheFixedPrefix ns params type.appArg! (index + 1) last
    pure <| mkApp2 (mkConst ``And) left tail
  else
    throwError "prescribed reference boundary: unexpected connective at {index}"
  addDefinition (ns.str s!"Prefix{index}") params (mkSort 0) value

private partial def selectFixedPrefix (ns : Name) (params : Array Expr)
    (proof : Expr) (index last : Nat) : MetaM Unit := do
  if index == last then
    discard <| addTheorem (ns.str "continuation") params (← inferType proof) proof
    return
  let type ← whnf (← inferType proof)
  if type.isAppOfArity ``Exists 2 then
    let predicate := type.appArg!
    let .lam name domain _ _ := predicate
      | throwError "prescribed reference boundary: expected cached existential predicate"
    let witnessValue ← mkAppM ``Classical.choose #[proof]
    let witness ← addDefinition (ns ++ name) params domain witnessValue
    let specification ← mkAppM ``Classical.choose_spec #[proof]
    let tail ← addTheorem (ns.str s!"selectedPrefix{index + 1}") params
      (predicate.beta #[witness]) specification
    selectFixedPrefix ns params tail (index + 1) last
  else if type.isAppOfArity ``And 2 then
    let left ← mkAppM ``And.left #[proof]
    discard <| addTheorem (ns.str s!"fact{index}") params type.appFn!.appArg! left
    let right ← mkAppM ``And.right #[proof]
    let tail ← addTheorem (ns.str s!"selectedPrefix{index + 1}") params type.appArg! right
    selectFixedPrefix ns params tail (index + 1) last
  else
    throwError "prescribed reference boundary: invalid cached connective at {index}"

private def generateFixed (source ns : Name) (last expectedParams : Nat) : Lean.Elab.Term.TermElabM Unit := do
  let info ← getConstInfo source
  unless info.levelParams.isEmpty do
    throwError "prescribed reference boundary: unexpected universe parameters"
  forallTelescopeReducing info.type fun params statement => do
    unless params.size == expectedParams do
      throwError "prescribed reference boundary: expected {expectedParams} original parameters, got {params.size}"
    let cached ← cacheFixedPrefix ns params statement 0 last
    let original := mkAppN (mkConst source) params
    let initialized ← addTheorem (ns.str "initialized") params cached original
    selectFixedPrefix ns params initialized 0 last

/-- Retain arbitrary orders, margins and caps while selecting the original
source-scaled reference, seed-result clause, leading and mean continuations. -/
elab "cache_prescribed_extension_callback_boundary" : command => liftTermElabM do
  generateFixed
    `JanetCartan.ContinuumInverse.InitializedCappedHistory.QuotientBoundary.continuation
    `JanetCartan.ContinuumInverse.InitializedCappedHistory.ReferenceBoundary 9 18

/-- Select the original seed chart family and retain its original incidence
and all-cell source callbacks from the same source-scaled reference. -/
elab "cache_prescribed_seed_boundary" : command => liftTermElabM do
  generateFixed
    `JanetCartan.ContinuumInverse.InitializedCappedHistory.ReferenceBoundary.fact7
    `JanetCartan.ContinuumInverse.InitializedCappedHistory.SeedBoundary 4 18

/-- Project the original same-row source inverse, retaining its original gap,
inner exterior and source-scale continuations rather than selecting a second one. -/
elab "cache_prescribed_source_inverse_boundary" : command => liftTermElabM do
  generateFixed
    `JanetCartan.ContinuumInverse.InitializedCappedHistory.SelectedBoundary.fact98
    `JanetCartan.ContinuumInverse.InitializedCappedHistory.SourceInverseBoundary 28 21

end JanetCartan.ContinuumInverse.InitializedCappedHistory.ReferenceBoundary.Generator

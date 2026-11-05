module

public meta import Lean

/-!
# Literal projections for the strengthened inverse's fixed geometry

The first command projects the same strengthened contraction's legacy empty
history interface solely to prove history-independent working-ball containment.
It is never used for a physical Schwartz prefix.  The second command projects
the exact selected conic chart clauses required by the current inverse.
Every declaration is ordinary, safe and kernel checked; no row is reselected.
-/

public meta section
namespace JanetCartan.PhysicalNormalInverse.StrongGeometryApplication
open Lean Meta Elab Command

private def addDef (name : Name) (params : Array Expr) (type value : Expr) : MetaM Expr := do
  addDecl (.defnDecl {
    name, levelParams := [], type := ← mkForallFVars params type,
    value := ← mkLambdaFVars params value,
    hints := .abbrev, safety := .safe }) (forceExpose := true)
  return mkAppN (mkConst name) params

private def addThm (name : Name) (params : Array Expr) (type value : Expr) : MetaM Expr := do
  addDecl (.thmDecl {
    name, levelParams := [], type := ← mkForallFVars params type,
    value := ← mkLambdaFVars params value }) (forceExpose := true)
  return mkAppN (mkConst name) params

private partial def cache (ns : Name) (params : Array Expr) (type : Expr)
    (index last : Nat) : MetaM Expr := do
  if index == last then
    return ← addDef (ns.str "Continuation") params (mkSort 0) type
  let type ← whnf type
  let value ← if type.isAppOfArity ``Exists 2 then
    match type.appArg! with
    | .lam name domain body _ =>
      withLocalDeclD name domain fun witness => do
        let tail ← cache ns (params.push witness) (body.instantiate1 witness) (index + 1) last
        mkAppM ``Exists #[← mkLambdaFVars #[witness] tail]
    | _ => throwError "strong empty geometry: expected existential predicate"
  else if type.isAppOfArity ``And 2 then do
    let left ← addDef (ns.str s!"FactType{index}") params (mkSort 0) type.appFn!.appArg!
    let tail ← cache ns params type.appArg! (index + 1) last
    pure <| mkApp2 (mkConst ``And) left tail
  else
    throwError "strong empty geometry: unexpected connective at {index}"
  addDef (ns.str s!"Prefix{index}") params (mkSort 0) value

private partial def select (ns : Name) (params : Array Expr) (proof : Expr)
    (index last : Nat) : MetaM Unit := do
  if index == last then
    discard <| addThm (ns.str "continuation") params (← inferType proof) proof
    return
  let type ← whnf (← inferType proof)
  if type.isAppOfArity ``Exists 2 then
    let predicate := type.appArg!
    let .lam name domain _ _ := predicate
      | throwError "strong empty geometry: invalid cached existential"
    let witnessValue ← mkAppM ``Classical.choose #[proof]
    let witness ← addDef (ns ++ name) params domain witnessValue
    let specification ← mkAppM ``Classical.choose_spec #[proof]
    let tail ← addThm (ns.str s!"selectedPrefix{index + 1}") params
      (predicate.beta #[witness]) specification
    select ns params tail (index + 1) last
  else if type.isAppOfArity ``And 2 then
    let left ← mkAppM ``And.left #[proof]
    discard <| addThm (ns.str s!"fact{index}") params type.appFn!.appArg! left
    let right ← mkAppM ``And.right #[proof]
    let tail ← addThm (ns.str s!"selectedPrefix{index + 1}") params type.appArg! right
    select ns params tail (index + 1) last
  else
    throwError "strong empty geometry: invalid cached connective at {index}"

private def generate (source ns : Name) (last expectedParams : Nat) : Term.TermElabM Unit := do
  let info ← getConstInfo source
  unless info.levelParams.isEmpty do
    throwError "strong empty geometry: unexpected universe parameters"
  forallTelescopeReducing info.type fun params statement => do
    unless params.size == expectedParams do
      throwError "strong empty geometry: expected {expectedParams} parameters, got {params.size}"
    let cached ← cache ns params statement 0 last
    let initialized ← addThm (ns.str "initialized") params cached (mkAppN (mkConst source) params)
    select ns params initialized 0 last

/-- These literal interfaces are used only at the empty history to deduce fixed
working-ball geometry on the SAME strengthened initializer. -/
elab "cache_strong_empty_geometry_inputs" : command => liftTermElabM do
  generate `JanetCartan.PhysicalSeed.ContractionBoundary.fact12
    `JanetCartan.PhysicalNormalInverse.StrongGeometry.EmptyLeading 13 31
  generate `JanetCartan.PhysicalNormalInverse.StrongGeometry.EmptyLeading.continuation
    `JanetCartan.PhysicalNormalInverse.StrongGeometry.EmptyAdmitted 8 37

/-- Project the exact eleven inverse-geometry clauses from this selected conic
row once, without re-elaborating the large source conjunction at each use. -/
elab "project_strong_current_conic_geometry" : command => liftTermElabM do
  let source := `JanetCartan.PhysicalNormalInverse.StrongConic.geometry
  let info ← getConstInfo source
  unless info.levelParams.isEmpty do
    throwError "strong inverse geometry: unexpected universe parameters"
  forallTelescopeReducing info.type fun params _ => do
    unless params.size == 28 do
      throwError "strong inverse geometry: expected 28 complete original/map inputs, got {params.size}"
    let original := mkAppN (mkConst source) params
    let primitive ← mkAppM ``And.left #[original]
    let spec ← mkAppM ``And.left #[← mkAppM ``And.right #[original]]
    let mut fields : Array Expr := #[]
    let mut rest := spec
    for _ in [:7] do
      fields := fields.push (← mkAppM ``And.left #[rest])
      rest ← mkAppM ``And.right #[rest]
    fields := fields.push rest
    fields := fields.push (← mkAppM ``And.left #[primitive])
    let primitiveTail ← mkAppM ``And.right #[← mkAppM ``And.right #[primitive]]
    fields := fields.push (← mkAppM ``And.left #[primitiveTail])
    fields := fields.push (← mkAppM ``And.left #[← mkAppM ``And.right #[primitiveTail]])
    let mut proof := fields.back!
    for index in [:fields.size - 1] do
      proof ← mkAppM ``And.intro #[fields[fields.size - 2 - index]!, proof]
    discard <| addThm `JanetCartan.PhysicalNormalInverse.StrongConic.current_geometry
      params (← inferType proof) proof

/-- Retain the numerical inverse cap and scalar budget from the actual strong
geometric application; the original row and all geometry stay unchanged. -/
elab "cache_strong_current_inverse_cap" : command => liftTermElabM do
  generate `JanetCartan.PhysicalNormalInverse.StrongCurrent.initialized
    `JanetCartan.PhysicalNormalInverse.StrongCurrent.Cap 7 21

end JanetCartan.PhysicalNormalInverse.StrongGeometryApplication

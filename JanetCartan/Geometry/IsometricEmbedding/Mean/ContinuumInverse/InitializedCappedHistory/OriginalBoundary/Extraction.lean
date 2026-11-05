module

public meta import Lean

/-!
# Exact prefix caching for the strong prescribed common initializer

Factor the strong prescribed existential/conjunction prefix, including its
retained generic leading field, before the complete original `εframe` callback.
Each generated object is an ordinary kernel-checked definition or theorem with
the literal stronger body. No witness is supplied as an added analytic
hypothesis. This specializes the checked prefix-cache method of
`AdmittedDecayBoundary.Extraction` to the prescribed density-product initializer.
-/

public meta section

namespace JanetCartan.ContinuumInverse.InitializedCappedHistory.OriginalBoundary.Generator
open Lean Meta Elab Command

private def boundaryNamespace : Name :=
  `JanetCartan.ContinuumInverse.InitializedCappedHistory.OriginalBoundary

private def stepName (index : Nat) : Name := boundaryNamespace.str s!"Prefix{index}"
private def selectedName (index : Nat) : Name := boundaryNamespace.str s!"selectedPrefix{index}"
private def factName (index : Nat) : Name := boundaryNamespace.str <|
  match index with
  | 1 => "reference_analytic"
  | 4 => "b_pos"
  | 5 => "b_lt_R"
  | 6 => "R_lt_chartRadius"
  | 12 => "kCenter_mem_sphere"
  | 13 => "kCenter_mem_domain"
  | 15 => "flow_contDiffOn"
  | 16 => "stateDomain_subset_ball"
  | 17 => "innerState_certificate"
  | 19 => "gamma_pos"
  | 20 => "frozen_transversality"
  | 22 => "r_pos"
  | 23 => "three_mul_r_lt_b"
  | 24 => "three_mul_r_lt_referenceRadius"
  | 26 => "leadTolerance_pos"
  | 39 => "comparison_reserve"
  | 40 => "comparison_pos"
  | 47 => "cofactor_cells"
  | 48 => "leading_cells"
  | 49 => "transport_cells"
  | 50 => "comparison_cover"
  | 53 => "carrier_cells"
  | 54 => "carrier_cover"
  | 56 => "parameter_cover"
  | 59 => "density_product_geometry"
  | 60 => "density_product_cover"
  | 61 => "generic_leading_exists"
  | _ => s!"fact{index}"

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

private partial def cachePrefix (params : Array Expr) (type : Expr)
    (index : Nat) : MetaM Expr := do
  let value ← if type.isAppOfArity ``Exists 2 then
    match type.appArg! with
    | .lam name domain body _ =>
      withLocalDeclD name domain fun witness => do
        let tail ← cachePrefix (params.push witness) (body.instantiate1 witness) (index + 1)
        mkAppM ``Exists #[← mkLambdaFVars #[witness] tail]
    | _ => throwError "prescribed boundary: expected a literal existential predicate"
  else if type.isAppOfArity ``And 2 then do
    let tail ← cachePrefix params type.appArg! (index + 1)
    pure <| mkApp2 (mkConst ``And) type.appFn!.appArg! tail
  else
    match type with
    | .forallE name _ _ _ =>
      unless index == 62 && name == `εframe do
        throwError "prescribed boundary changed: expected εframe at prefix 62, got {name} at {index}"
      return ← addDefinition (boundaryNamespace.str "Continuation") params (mkSort 0) type
    | _ => throwError "prescribed boundary: unexpected final connective"
  addDefinition (stepName index) params (mkSort 0) value

private partial def selectPrefix (params : Array Expr) (proof : Expr)
    (index : Nat) : MetaM Unit := do
  if index == 62 then
    discard <| addTheorem (boundaryNamespace.str "continuation") params (← inferType proof) proof
    return
  let type ← whnf (← inferType proof)
  if type.isAppOfArity ``Exists 2 then
    let predicate := type.appArg!
    let .lam name domain _ _ := predicate
      | throwError "prescribed boundary: cached existential is not a lambda"
    let witnessValue ← mkAppM ``Classical.choose #[proof]
    let witness ← addDefinition (boundaryNamespace ++ name) params domain witnessValue
    let specification ← mkAppM ``Classical.choose_spec #[proof]
    let tailType := predicate.beta #[witness]
    let tail ← addTheorem (selectedName (index + 1)) params tailType specification
    selectPrefix params tail (index + 1)
  else if type.isAppOfArity ``And 2 then
    let left ← mkAppM ``And.left #[proof]
    discard <| addTheorem (factName index) params type.appFn!.appArg! left
    let right ← mkAppM ``And.right #[proof]
    let tail ← addTheorem (selectedName (index + 1)) params type.appArg! right
    selectPrefix params tail (index + 1)
  else
    throwError "prescribed boundary: cached prefix {index} is neither Exists nor And"

/-- Select one strong prescribed initializer, retaining arbitrary-map generic
leading and the complete original quotient/extension/cap/source/mean callback. -/
elab "cache_prescribed_common_initializer_boundary" : command => liftTermElabM do
  let source := `JanetCartan.PhysicalSeed.exists_prescribed_source_with_generic_leading
  let info ← getConstInfo source
  unless info.levelParams.isEmpty do
    throwError "prescribed boundary: unexpected universe parameters"
  forallTelescope info.type fun params statement => do
    unless params.size == 2 do
      throwError "prescribed boundary: expected dimension and its lower bound"
    let cached ← cachePrefix params statement 0
    let original := mkAppN (mkConst source) params
    let initialized ← addTheorem (boundaryNamespace.str "initialized") params cached original
    selectPrefix params initialized 0
    let generic := mkAppN (mkConst (boundaryNamespace.str "generic_leading_exists")) params
    let type ← whnf (← inferType generic)
    unless type.isAppOfArity ``Exists 2 do
      throwError "prescribed boundary: missing generic tolerance existential"
    let predicate := type.appArg!
    let witnessValue ← mkAppM ``Classical.choose #[generic]
    let witness ← addDefinition (boundaryNamespace.str "η") params (← inferType witnessValue) witnessValue
    let specification ← mkAppM ``Classical.choose_spec #[generic]
    let specification ← addTheorem (boundaryNamespace.str "generic_specification") params
      (predicate.beta #[witness]) specification
    let positive ← mkAppM ``And.left #[specification]
    discard <| addTheorem (boundaryNamespace.str "η_pos") params (← inferType positive) positive
    let leading ← mkAppM ``And.right #[specification]
    discard <| addTheorem (boundaryNamespace.str "generic_leading") params (← inferType leading) leading

private partial def cacheCallbackPrefix (ns : Name) (expectedBinder : Name)
    (params : Array Expr) (type : Expr) (index : Nat) : MetaM (Expr × Nat) := do
  let type ← whnf type
  let (value, last) ← if type.isAppOfArity ``Exists 2 then
    match type.appArg! with
    | .lam name domain body _ =>
      withLocalDeclD name domain fun witness => do
        let (tail, last) ← cacheCallbackPrefix ns expectedBinder (params.push witness)
          (body.instantiate1 witness) (index + 1)
        return (← mkAppM ``Exists #[← mkLambdaFVars #[witness] tail], last)
    | _ => throwError "prescribed callback: expected literal existential predicate"
  else if type.isAppOfArity ``And 2 then do
    let (tail, last) ← cacheCallbackPrefix ns expectedBinder params type.appArg! (index + 1)
    pure (mkApp2 (mkConst ``And) type.appFn!.appArg! tail, last)
  else
    match type with
    | .forallE name _ _ _ =>
      unless name == expectedBinder do
        throwError "prescribed callback changed: expected {expectedBinder}, got {name} at {index}"
      return (← addDefinition (ns.str "Continuation") params (mkSort 0) type, index)
    | _ => throwError "prescribed callback: unexpected final connective at {index}"
  return (← addDefinition (ns.str s!"Prefix{index}") params (mkSort 0) value, last)

private partial def selectCallbackPrefix (ns : Name) (params : Array Expr)
    (proof : Expr) (index last : Nat) : MetaM Unit := do
  if index == last then
    discard <| addTheorem (ns.str "continuation") params (← inferType proof) proof
    return
  let type ← whnf (← inferType proof)
  if type.isAppOfArity ``Exists 2 then
    let predicate := type.appArg!
    let .lam name domain _ _ := predicate
      | throwError "prescribed callback: cached existential is not a lambda"
    let witnessValue ← mkAppM ``Classical.choose #[proof]
    let witness ← addDefinition (ns ++ name) params domain witnessValue
    let specification ← mkAppM ``Classical.choose_spec #[proof]
    let tail ← addTheorem (ns.str s!"selectedPrefix{index + 1}") params
      (predicate.beta #[witness]) specification
    selectCallbackPrefix ns params tail (index + 1) last
  else if type.isAppOfArity ``And 2 then
    let left ← mkAppM ``And.left #[proof]
    discard <| addTheorem (ns.str s!"fact{index}") params type.appFn!.appArg! left
    let right ← mkAppM ``And.right #[proof]
    let tail ← addTheorem (ns.str s!"selectedPrefix{index + 1}") params type.appArg! right
    selectCallbackPrefix ns params tail (index + 1) last
  else
    throwError "prescribed callback: cached prefix {index} is neither Exists nor And"

/-- Apply the original quotient callback to arbitrary inputs, caching only its
exact output prefix before the unchanged extension-order/margin/cap callback. -/
elab "cache_prescribed_quotient_callback_boundary" : command => liftTermElabM do
  let source := `JanetCartan.ContinuumInverse.InitializedCappedHistory.OriginalBoundary.continuation
  let ns := `JanetCartan.ContinuumInverse.InitializedCappedHistory.QuotientBoundary
  let info ← getConstInfo source
  unless info.levelParams.isEmpty do
    throwError "prescribed quotient callback: unexpected universe parameters"
  forallTelescopeReducing info.type fun params statement => do
    unless params.size == 10 do
      throwError "prescribed quotient callback: expected ten original parameters, got {params.size}"
    let statement ← whnf statement
    let (cached, last) ← cacheCallbackPrefix ns `p params statement 0
    let original := mkAppN (mkConst source) params
    let initialized ← addTheorem (ns.str "initialized") params cached original
    selectCallbackPrefix ns params initialized 0 last

/-- Apply the original incidence callback to arbitrary positive cap functions.
The caller may supply its minimum with the checked original raw cap. Every
selected row, source flow, inverse and exterior remains on that application. -/
elab "cache_prescribed_incidence_callback_boundary" : command => liftTermElabM do
  let source := `JanetCartan.ContinuumInverse.InitializedCappedHistory.OriginalAngularSourceCallback.initialized
  let ns := `JanetCartan.ContinuumInverse.InitializedCappedHistory.SelectedBoundary
  let info ← getConstInfo source
  unless info.levelParams.isEmpty do
    throwError "prescribed incidence callback: unexpected universe parameters"
  forallTelescopeReducing info.type fun params statement => do
    unless params.size == 21 do
      throwError "prescribed incidence callback: expected twenty-one original parameters, got {params.size}"
    let statement ← whnf statement
    let (cached, last) ← cacheCallbackPrefix ns `targetGap params statement 0
    let original := mkAppN (mkConst source) params
    let initialized ← addTheorem (ns.str "initialized") params cached original
    selectCallbackPrefix ns params initialized 0 last

end JanetCartan.ContinuumInverse.InitializedCappedHistory.OriginalBoundary.Generator

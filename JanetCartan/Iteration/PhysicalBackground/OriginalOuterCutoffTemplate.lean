module

public meta import Lean

/-!
# Replay the actual static product geometry for one protected outer cutoff

The consuming command is in `OriginalOuterCutoff`. It reuses the actual
original21 geometry, intersects its old product collar with the original
strict parameter window, and chooses one NEW external weight there before
σ/history/source. It does not use or identify the old SourceFull χ.
-/

public meta section
namespace JanetCartan.PhysicalBackground.OriginalOuterCutoffTemplate
open Lean Meta Elab Command Term

def targetNS := `JanetCartan.PhysicalBackground.OriginalOuterCutoff

def store (field : Name) (params : Array Expr) (term : Expr)
    (data : Bool := false) : MetaM Expr := do
  let name := targetNS ++ field
  let type ← instantiateMVars (← mkForallFVars params (← inferType term))
  let value ← instantiateMVars (← mkLambdaFVars params term)
  if type.hasMVar || value.hasMVar || type.hasFVar || value.hasFVar ||
      type.hasLevelMVar || value.hasLevelMVar || type.hasSorry || value.hasSorry then
    throwError "original outer cutoff: incomplete static declaration {name}"
  if data then
    addDecl (.defnDecl { name, type, value, levelParams := [], hints := .abbrev, safety := .safe })
      (forceExpose := true)
  else
    addDecl (.thmDecl { name, type, value, levelParams := [] }) (forceExpose := true)
  return mkAppN (mkConst name) params

def component (proof : Expr) (i : Nat) : Expr :=
  .proj ``And 0 (Nat.repeat (fun p => Expr.proj ``And 1 p) i proof)

/-- Construct one actual original21 outer weight in the protected open window;
no cap is applied here, so callers pass their already selected native21. -/
elab "construct_original_protected_outer_cutoff" : command => liftTermElabM do
  let original := `JanetCartan.PhysicalBackground.exists_original_product_weights
  let producer := `JanetCartan.PositiveBackground.exists_selected_product_external_weights
  let info ← getConstInfo original
  let some body := info.value? (allowOpaque := true) |
    throwError "original outer cutoff: original product proof needs import all"
  let arity ← forallTelescope (← getConstInfo producer).type fun xs _ => pure xs.size
  forallTelescope info.type fun params _ => do
    unless params.size == 21 do throwError "original outer cutoff: expected exactly selected original21"
    let mut proof ← Core.betaReduce (← zetaReduce (body.beta params))
    -- The old static proof opens an arithmetic kMin witness before constructing
    -- hselected. Close that EXISTS eliminator with its own choice/spec. This
    -- does not choose an old outer weight or a physical source/current.
    for _ in [:8] do
      let some application := proof.find? (·.isAppOfArity producer arity) |
        throwError "original outer cutoff: exact static product-geometry application missing"
      if !application.hasLooseBVars then break
      let some head := proof.getAppFn.constName? |
        throwError "original outer cutoff: static geometry eliminator is not a constant"
      unless head == ``Exists.elim || head == ``Exists.casesOn || head == ``Exists.rec ||
          head == `Exists.recOn do
        throwError "original outer cutoff: unsupported static geometry eliminator {head}"
      let eliminationArgs := proof.getAppArgs
      let mut existence : Option Expr := none
      for arg in eliminationArgs do
        let argType ← inferType arg
        if argType.isAppOf ``Exists then existence := some arg
      let some hExists := existence |
        throwError "original outer cutoff: static existential witness not found"
      let choice ← mkAppM ``Classical.choose #[hExists]
      let choiceSpec ← mkAppM ``Classical.choose_spec #[hExists]
      let branch := if head == ``Exists.rec then eliminationArgs[eliminationArgs.size - 2]!
        else eliminationArgs.back!
      let closed := mkAppN branch #[choice, choiceSpec]
      unless ← isDefEq (← inferType closed) (← inferType proof) do
        throwError "original outer cutoff: arithmetic witness replay changed the original proposition"
      proof ← Core.betaReduce (← zetaReduce closed)
    let some application := proof.find? (·.isAppOfArity producer arity) |
      throwError "original outer cutoff: exact static product-geometry application missing"
    if application.hasLooseBVars then
      throwError "original outer cutoff: product geometry still depends on a later witness"
    let mut oldType := (← getConstInfo producer).type
    let mut fields : Array (Name × Expr) := #[]
    for arg in application.getAppArgs do
      let .forallE name _ next _ := oldType |
        throwError "original outer cutoff: product geometry telescope changed"
      fields := fields.push (name.eraseMacroScopes, arg)
      oldType := next.instantiate1 arg
    let get (name : Name) : TermElabM Expr := do
      let some (_, value) := fields.find? (fun p => p.1 == name) |
        throwError "original outer cutoff: missing product geometry {name}"
      pure value
    let index ← get `A
    let oldV ← get `V
    let oldHV ← get `hV
    let oldSelected ← get `hselected
    let sampled := mkAppN (mkConst `JanetCartan.PhysicalSeed.SelectedBoundary.fact31) params
    let (window, radius, hopen, hselected) ← withLocalDeclD `i index fun i => do
      let parameterMap := component (mkApp sampled i) 1
      let parameterMapType ← Core.betaReduce (← zetaReduce (← inferType parameterMap))
      unless parameterMapType.isAppOf `Set.MapsTo do
        throwError "original outer cutoff: native fact31.2.1 is not its full carrier parameter map"
      let parameterWindow := parameterMapType.getAppArgs.back!
      unless parameterWindow.isAppOf
          `JanetCartan.FrozenMenu.parameterInterior do
        throwError "original outer cutoff: native strict patch parameter window changed"
      let radius := parameterWindow.getAppArgs.back!
      let window ← mkAppM `JanetCartan.PhysicalBackground.originalOuterWindow #[mkApp oldV i, radius]
      let hopen ← mkAppM `JanetCartan.PhysicalBackground.originalOuterWindow_open #[mkApp oldHV i, radius]
      let hselected ← mkAppM `JanetCartan.PhysicalBackground.originalOuterWindow_supported
        #[mkApp oldSelected i, parameterMap]
      return (← mkLambdaFVars #[i] window, ← mkLambdaFVars #[i] radius,
        ← mkLambdaFVars #[i] hopen, ← mkLambdaFVars #[i] hselected)
    let window ← store `window params window true
    discard <| store `parameterRadius params radius true
    discard <| store `root params (← get `zRoot) true
    discard <| store `a params (← get `am) true
    discard <| store `Voriginal params oldV true
    discard <| store `hV params oldHV
    discard <| store `hwindow params hopen
    let mut args := application.getAppArgs
    for j in [:fields.size] do
      let name := fields[j]!.1
      if name == `V then args := args.set! j window
      else if name == `hV then args := args.set! j hopen
      else if name == `hselected then args := args.set! j hselected
    let existsCutoff ← store `exists_cutoff params (mkAppN application.getAppFn args)
    discard <| store `χ params (← mkAppM ``Classical.choose #[existsCutoff]) true
    let spec ← store `spec params (← mkAppM ``Classical.choose_spec #[existsCutoff])
    for (name, i) in #[(`smooth, 0), (`range, 1), (`compact, 2), (`support_window, 3),
        (`plateau, 4), (`product_buffer, 5), (`squared_smooth, 6), (`squared_nonneg, 7),
        (`squared_support, 8), (`finite, 9)] do
      discard <| store name params (component spec i)
    let support := component spec 3
    let plateau := component spec 4
    let (originalSupport, parameterSupport, signedSupport, offParameter, onCarrier) ← withLocalDeclD `i index fun i => do
      let originalSupport ← mkAppM `JanetCartan.PhysicalBackground.originalOuterWindow_support_original
        #[mkApp support i]
      let parameterSupport ← mkAppM `JanetCartan.PhysicalBackground.originalOuterWindow_support_parameter
        #[mkApp support i]
      let signedSupport ← mkAppM `JanetCartan.PhysicalBackground.originalOuterWindow_support_signed
        #[mkApp support i]
      let offParameter ← mkAppM `JanetCartan.PhysicalBackground.originalOuterWindow_off_parameter
        #[mkApp support i]
      let onCarrier ← mkAppM `JanetCartan.PhysicalBackground.originalOuterWindow_on_carrier
        #[mkApp plateau i]
      return (← mkLambdaFVars #[i] originalSupport, ← mkLambdaFVars #[i] parameterSupport,
        ← mkLambdaFVars #[i] signedSupport, ← mkLambdaFVars #[i] offParameter,
        ← mkLambdaFVars #[i] onCarrier)
    discard <| store `support_original params originalSupport
    discard <| store `support_parameter params parameterSupport
    discard <| store `support_signed params signedSupport
    discard <| store `off_parameter params offParameter
    discard <| store `on_carrier params onCarrier
    discard <| store `mask_spec params (Nat.repeat (fun p => Expr.proj ``And 1 p) 10 spec)
    logInfo "constructed ONE original21 outer χ inside V∩parameter⁻¹interior(P.radius), whole native carrier plateau; no caps, source, inverse or old χ replaced"

end JanetCartan.PhysicalBackground.OriginalOuterCutoffTemplate
end

module

public meta import Lean
public meta import JanetCartan.Iteration.PhysicalNormalInverse.StrongToleranceApplication

/-!
# Replay the actual original source for physical density mean continuity

Reuse the already checked 134-argument source application, discard its six
history-order parameters, and keep the literal source-zero angular mask.
Only the unchanged compact parameter weight and its original support
certificates remain universal. No selector or capped callback is replayed.
-/

public meta section
namespace JanetCartan.PhysicalDensityContinuity.StrongApplication
open Lean Meta Elab Command

private def termAt (code : String) (type : Expr) : TermElabM Expr := Term.withoutErrToSorry do
  let stx ← match Parser.runParserCategory (← getEnv) `term code with
    | .ok stx => pure stx
    | .error e => throwError "source density mean: term parser: {e}"
  let value ← Term.elabTermEnsuringType stx type
  Term.synthesizeSyntheticMVarsNoPostponing
  let value ← instantiateMVars value
  if value.hasMVar || value.hasSorry then
    throwError "source density mean: incomplete argument proof in {code}"
  return value

private def store (name : Name) (params : Array Expr) (value : Expr) : MetaM Unit := do
  let fullName := `JanetCartan.PhysicalDensityContinuity.StrongDensity ++ name
  let type ← mkForallFVars params (← inferType value)
  let value ← mkLambdaFVars params value
  if type.hasMVar || value.hasMVar || type.hasSorry || value.hasSorry then
    throwError "source density mean: incomplete generated declaration {fullName}"
  if type.hasFVar || value.hasFVar then
    let t := if type.hasFVar then type else value
    let some x := t.find? (·.isFVar) | throwError "source density mean: open declaration {fullName}"
    throwError "source density mean: unexpected dependence on {(← x.fvarId!.getDecl).userName}"
  addDecl (.thmDecl { name := fullName, levelParams := [], type, value }) (forceExpose := true)

/-- Specialize the genuine physical mean producer to the SAME original23
source and source-zero chart; do not reapply the extra cap or choose a row. -/
elab "realize_strong_source_density_mean_tolerance" : command => liftTermElabM do
  let source := `JanetCartan.PhysicalNormalInverse.StrongSource.exists_history_coercivity
  let old := `JanetCartan.PhysicalNormalInverse.exists_prescribed_source_history_coercivity
  let consumer := `JanetCartan.PhysicalDensityContinuity.exists_prescribed_source_density_mean_tolerance
  let info ← getConstInfo source
  unless info.levelParams.isEmpty do throwError "source density mean: unexpected source universes"
  forallBoundedTelescope info.type (some 29) fun params _ => do
    unless params.size == 29 do throwError "source density mean: expected original23 plus six order arguments"
    let args ← PhysicalNormalInverse.StrongToleranceApplication.actualSourceArguments params
    let original := params[:23].toArray
    let extra := params[23:].toArray
    let occurs := fun (t : Expr) ↦ t.hasAnyFVar (fun id ↦ extra.any (fun p ↦ p.fvarId! == id))
    let staticArg (arg : Expr) : MetaM Expr := do
      if !occurs arg then return arg
      let some name := arg.getAppFn.constName? | throwError "source density mean: composite nonstatic selector"
      unless (`JanetCartan.PhysicalNormalInverse.StrongSource.Arguments).isPrefixOf name do
        throwError "source density mean: nonstatic selector {name}"
      let value := ((← getConstInfo name).value! (allowOpaque := true)).beta arg.getAppArgs
      if occurs value then throwError "source density mean: genuinely order-dependent proof {name}"
      return value
    let mut cache : Array (Name × Expr) := #[]
    let mut oldType := (← getConstInfo old).type
    for arg in args do
      let .forallE name _ body _ := oldType | throwError "source density mean: original134 telescope changed"
      cache := cache.push (name.eraseMacroScopes, arg)
      if name == `hcoeff₀ then break
      oldType := body.instantiate1 arg
    let lookup (name : Name) : MetaM Expr := do
      let some (_, arg) := cache.find? (fun p ↦ p.1 == name) |
        throwError "source density mean: missing original argument {name}"
      staticArg arg
    let dataName := `JanetCartan.ContinuumRow.CanonicalCarrier.data
    let dataArity ← forallTelescope (← getConstInfo dataName).type fun xs _ => pure xs.size
    let actions := mkAppN
      (mkConst `JanetCartan.PhysicalInverseContinuity.StrongRaw.reference_adjoint_action) original
    let angular ← forallBoundedTelescope (← inferType actions) (some 1) fun indices body => do
      unless indices.size == 1 do throwError "source density mean: expected actual carrier index"
      let some d := body.find? (fun e ↦ e.isAppOfArity dataName dataArity) |
        throwError "source density mean: literal source-zero carrier data not found"
      let fields := d.getAppArgs
      mkLambdaFVars indices fields[fields.size - 2]!
    let hμr := mkAppN (mkConst `JanetCartan.PhysicalSeed.SelectedBoundary.fact60) original[:21]
    let mut type := (← getConstInfo consumer).type
    let mut selected : Array Expr := #[]
    for _ in [:args.size] do
      let .forallE name dom body _ := type | throwError "source density mean: missing unchanged weight telescope"
      if name == `χ then break
      let arg ← if name == `angular then pure angular
        else if name == `hμr then pure hμr
        else if name == `Voriginal then lookup `V
        else if name == `hVoriginal then lookup `hV
        else if name == `hDregion then do
          let region ← lookup `hDregion
          withLetDecl `originalRegion (← inferType region) region fun r => do
            let t ← termAt "by intro i; exact (originalRegion i).trans inter_subset_left" dom
            return t.replaceFVar r region
        else lookup name.eraseMacroScopes
      selected := selected.push arg
      type := body.instantiate1 arg
    let .forallE name _ _ _ := type | throwError "source density mean: missing carrier weight"
    unless name == `χ do throwError "source density mean: did not reach unchanged carrier weight"
    forallBoundedTelescope type (some 4) fun weights _ => do
      unless weights.size == 4 do throwError "source density mean: expected weight and three original certificates"
      let proof := mkAppN (mkConst consumer) (selected ++ weights)
      store `exists_source_density_mean_tolerance (original ++ weights) proof
      logInfo m!"checked {selected.size} actual original static arguments; original23 only plus SAME carrier weight/support; exact source-zero angular mask; no mean or field continuity premise"

end JanetCartan.PhysicalDensityContinuity.StrongApplication

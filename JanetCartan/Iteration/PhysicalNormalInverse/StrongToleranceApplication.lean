module

public meta import Lean

/-!
# Replay the exact strengthened source arguments for a normal tolerance

Reuse the actual checked134-argument application, not another selection. Only
ε and its positivity are appended to the generic comparison consumer. Close its
source operator with the already retained `StrongSourceGap.Vop` and test action.
The final continuation is universal in the actual current coefficients/operators.
-/

public meta section
namespace JanetCartan.PhysicalNormalInverse.StrongToleranceApplication
open Lean Meta Elab Command

/-- The exact actual source argument vector, preserved for the fixed-scale strong
raw-continuity application as well as the normal comparison. -/
def actualSourceArguments (params : Array Expr) : MetaM (Array Expr) := do
  unless params.size == 29 do
    throwError "strong tolerance: expected original29 source/history parameters"
  let .thmInfo info ← getConstInfo
      `JanetCartan.PhysicalNormalInverse.StrongSource.exists_history_coercivity |
    throwError "strong tolerance: actual source application is not a theorem"
  let proof ← Core.betaReduce (← zetaReduce (info.value.beta params))
  unless proof.isAppOfArity
      `JanetCartan.PhysicalNormalInverse.exists_prescribed_source_history_coercivity 134 do
    throwError "strong tolerance: actual134 source application changed"
  if proof.hasMVar || proof.hasSorry then
    throwError "strong tolerance: incomplete source argument extraction"
  return proof.getAppArgs

private def checkClosed (type value : Expr) : MetaM Unit := do
  if type.hasMVar || value.hasMVar || type.hasFVar || value.hasFVar ||
      type.hasSorry || value.hasSorry then
    throwError "strong tolerance: open or recovered generated declaration"

private def addTheorem (name : Name) (params : Array Expr)
    (type value : Expr) : MetaM Expr := do
  let type ← mkForallFVars params (← instantiateMVars type)
  let value ← mkLambdaFVars params (← instantiateMVars value)
  checkClosed type value
  addDecl (.thmDecl { name, levelParams := [], type, value }) (forceExpose := true)
  return mkAppN (mkConst name) params

private def addDefinition (name : Name) (params : Array Expr)
    (value : Expr) : MetaM Expr := do
  let value ← instantiateMVars value
  let type ← mkForallFVars params (← inferType value)
  let value ← mkLambdaFVars params value
  checkClosed type value
  addDecl (.defnDecl {
    name, levelParams := [], type, value, hints := .abbrev, safety := .safe
  }) (forceExpose := true)
  return mkAppN (mkConst name) params

/-- Instantiate the arbitrary normal tolerance on precisely the existing strong
source tuple, with a fresh comparison threshold but no fresh source selection. -/
elab "apply_actual_strong_source_normal_tolerance" : command => liftTermElabM do
  let source := `JanetCartan.PhysicalNormalInverse.StrongSource.exists_history_coercivity
  let generic := `JanetCartan.PhysicalNormalInverse.exists_prescribed_source_history_normal_tolerance
  let sourceGap := `JanetCartan.PhysicalNormalInverse.StrongSourceGap
  let cache := `JanetCartan.PhysicalNormalInverse.StrongSource.NormalTolerance
  let info ← getConstInfo source
  unless info.levelParams.isEmpty do
    throwError "strong tolerance: source application gained universe parameters"
  forallBoundedTelescope info.type (some 29) fun sourceParams _ => do
    let args ← actualSourceArguments sourceParams
    let staticApplied := mkAppN (mkConst generic) args[:133]
    forallBoundedTelescope (← inferType staticApplied) (some 2) fun tolerance _ => do
      unless tolerance.size == 2 do
        throwError "strong tolerance: expected epsilon and its positivity"
      let params := sourceParams ++ tolerance
      let raw := mkAppN staticApplied (tolerance ++ #[args.back!])
      let rawType ← whnf (← inferType raw)
      unless rawType.isAppOfArity ``Exists 2 do
        throwError "strong tolerance: expected a prehistory threshold"
      let S ← addDefinition (cache ++ `S) params (← mkAppM ``Classical.choose #[raw])
      let rawSpecValue ← mkAppM ``Classical.choose_spec #[raw]
      let rawSpec ← addTheorem (cache ++ `raw_spec) params
        (rawType.appArg!.beta #[S]) rawSpecValue
      let hSValue ← mkAppM ``And.left #[rawSpec]
      let hS ← addTheorem (cache ++ `hS) params (← inferType hSValue) hSValue
      let continuation ← mkAppM ``And.right #[rawSpec]
      let actual ← forallBoundedTelescope (← inferType continuation) (some 5) fun density _ => do
        unless density.size == 5 do
          throwError "strong tolerance: expected the original density certificates"
        let sourceAtDensity := sourceParams[:23].toArray ++ density
        let sourceOperator := mkAppN (mkConst (sourceGap ++ `Vop)) sourceAtDensity
        let sourceActions := mkAppN (mkConst (sourceGap ++ `actions)) sourceAtDensity
        let tests ← forallBoundedTelescope (← inferType sourceActions) (some 1) fun indices _ => do
          let proof ← mkAppM ``And.left #[mkAppN sourceActions indices]
          mkLambdaFVars indices (← instantiateMVars proof)
        let result := mkAppN (mkAppN continuation density) #[sourceOperator, tests]
        mkLambdaFVars density (← instantiateMVars result)
      let actual ← addTheorem (cache ++ `continuation) params (← inferType actual) actual
      let bundle ← mkAppM ``And.intro #[hS, actual]
      let bundleType ← instantiateMVars (← inferType bundle)
      let predicate ← withLocalDeclD `threshold (← inferType S) fun threshold => do
        let type := bundleType.replace fun e => if e == S then some threshold else none
        mkLambdaFVars #[threshold] type
      let result ← mkAppOptM ``Exists.intro
        #[none, some predicate, some S, some bundle]
      discard <| addTheorem
        `JanetCartan.PhysicalNormalInverse.StrongSource.exists_history_normal_tolerance
        params (← inferType result) result
      logInfo "kernel-checked actual original29 plus tolerance2; same source row, arbitrary tested current normal"

end JanetCartan.PhysicalNormalInverse.StrongToleranceApplication
end

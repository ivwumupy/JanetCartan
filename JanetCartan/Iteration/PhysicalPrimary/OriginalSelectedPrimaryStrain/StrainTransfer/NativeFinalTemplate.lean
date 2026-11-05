module

public meta import JanetCartan.Iteration.PhysicalPrimary.OriginalSelectedPrimaryStrain.StrainTransfer.NativeTemplate
public meta import JanetCartan.Iteration.PhysicalPrimary.OriginalSelectedPrimaryStrain.StrainTransfer.NativeContext
import all JanetCartan.Iteration.PhysicalPrimary.OriginalSelectedPrimaryStrain.StrainTransfer.NativeTemplate
public meta import Lean

/-! Actual source-to-strain composition through separately checked original
identities and differentiability. No source-decay or response-success input is
added (main:eq:lag-strain; main:eq:primary-strain). -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true
set_option Elab.async false

public meta section
namespace JanetCartan.PhysicalPrimary.OriginalSelectedPrimaryStrain.StrainTransfer.NativeFinalTemplate
open Lean Meta Elab Command

private def root := `JanetCartan.PhysicalPrimary.OriginalSelectedPrimaryStrain.StrainTransfer
private def dataRoot := `JanetCartan.PhysicalPrimary.OriginalSelectedPrimaryStrain.SourceData
private def raw := `JanetCartan.PhysicalPrimary.OriginalRawSourceField.Native
private def response := `JanetCartan.PhysicalSampling.OriginalGraphResponse
private def app (key : Name) (p : Array Expr) : Expr := mkAppN (mkConst key) p
private def helper (key : Name) : Name := mkPrivateNameCore
  `JanetCartan.Iteration.PhysicalPrimary.OriginalSelectedPrimaryStrain.StrainTransfer.NativeTemplate
  (root ++ `NativeTemplate ++ key)
private def termWith (p : List (Name × Expr)) (code : String) : MetaM Expr :=
  Term.TermElabM.run' (JanetCartan.PhysicalBackground.NativeReferenceSourceTemplate.termWith p code)
private def bodyAt (e : Expr) : MetaM Expr := do
  let ci ← getConstInfo e.getAppFn.constName!
  let some value := ci.value? (allowOpaque := true) |
    throwError "native strain application: missing original body {ci.name}"
  return ((value.instantiateLevelParams ci.levelParams e.getAppFn.constLevels!).beta e.getAppArgs).headBeta

private def save (key : Name) (p : Array Expr) (proof target : Expr)
    (description : String) : MetaM Unit := do
  let type ← instantiateMVars (← mkForallFVars p target)
  let value ← instantiateMVars (← mkLambdaFVars p proof)
  let env ← getEnv
  for e in #[type,value] do
    if e.hasFVar || e.hasMVar || e.hasLevelMVar || e.hasLevelParam ||
        e.hasLooseBVars || e.hasSorry then
      throwError "actual primary strain transfer: unresolved source/geometry/quadrature field {key}"
    let missing := e.getUsedConstants.filter fun c => (env.find? c).isNone
    unless missing.isEmpty do throwError "actual primary strain transfer: missing original metadata {missing.toList}"
  let (type,value) := Lean.ShareCommon.shareCommon (type,value)
  let name := root ++ key
  IO.println s!"Kernel checking actual original primary strain transfer {key}/{p.size}"
  (← IO.getStdout).flush
  addDecl (.thmDecl {name,levelParams := [],type,value}) (forceExpose := true)
  addDocStringCore name description
  let ax ← collectAxioms name
  unless ax.all (#[``propext,``Classical.choice,``Quot.sound].contains ·) do
    throwError "actual primary strain transfer: nonstandard axioms {ax}"
  logInfo m!"PASS actual original primary strain transfer {key}/{p.size}: {ax}"

private def equalityType (proof : Expr) : MetaM Expr := do
  let t ← inferType proof
  if t.isAppOfArity ``Eq 3 then return t
  let unfolded ← bodyAt t
  unless unfolded.isAppOfArity ``Eq 3 do
    throwError "native strain application: checked equality statement changed"
  return unfolded

elab "retain_original_native_primary_strain " mode:num : command => liftTermElabM do
  unless mode.getNat < 2 do throwError "native primary strain: invalid mode"
  NativeContext.withSource fun c => do
    let p := c.params[:53].toArray
    let n := mkApp (mkConst ``Nat.succ) p[0]!
    let realParams := p.push (mkConst ``Bool.false)
    let imaginaryParams := p.push (mkConst ``Bool.true)
    let quadR := app (root ++ `native_tensor_strain_le_discrepancy) realParams
    let quadI := app (root ++ `native_tensor_strain_le_discrepancy) imaginaryParams
    let atFrame ← inferType quadR
    unless atFrame.isForall do throwError "native strain composition: numerical frame slot changed"
    let triangle := app (root ++ `native_node_strain_le_tensor_errors) p
    withLocalDeclD `hFrameTolerance atFrame.bindingDomain! fun hGamma => do
      forallBoundedTelescope (← inferType triangle) (some 2) fun point savedTarget => do
        let target ← if savedTarget.isAppOfArity ``LE.le 4 then pure savedTarget else bodyAt savedTarget
        unless point.size == 2 && target.isAppOfArity ``LE.le 4 do
          throwError "native strain composition: original point/core changed"
        let args := target.getAppArgs
        let sum := args[3]!
        unless sum.isAppOfArity ``HAdd.hAdd 6 do throwError "native strain composition: tensor norm sum changed"
        let errors := sum.getAppArgs
        let errR := mkApp (app (dataRoot ++ `discrepancy) realParams) point[0]!
        let errI := mkApp (app (dataRoot ++ `discrepancy) imaginaryParams) point[0]!
        let epsR ← mkAppM ``Norm.norm #[errR]
        let epsI ← mkAppM ``Norm.norm #[errI]
        let C := app `JanetCartan.UniformStep.projectedStressResidualConstant #[n,p[1]!]
        let proof := app (helper `combine_quadrature_bounds)
          #[args[2]!,errors[4]!,errors[5]!,C,epsR,epsI,mkAppN triangle point,
            mkAppN (mkApp quadR hGamma) point,mkAppN (mkApp quadI hGamma) point]
        let params := p ++ #[hGamma] ++ point
        if mode.getNat == 0 then
          let type ← instantiateMVars (← mkForallFVars params (mkSort .zero))
          let value ← instantiateMVars (← mkLambdaFVars params (← inferType proof))
          for e in #[type,value] do
            if e.hasFVar || e.hasMVar || e.hasLevelMVar || e.hasLevelParam ||
                e.hasLooseBVars || e.hasSorry then
              throwError "native primary strain statement: unresolved original input"
          let (type,value) := Lean.ShareCommon.shareCommon (type,value)
          let name := root ++ `native_node_strain_le_discrepancies_statement
          addDecl (.defnDecl {name,levelParams := [],type,value,hints := .regular 0,safety := .safe}) (forceExpose := true)
          addDocStringCore name "The exact original full complex-node strain inequality against the sum of its two named source discrepancies. This definition records the proposition, not its proof (main:eq:lag-strain; main:eq:primary-strain)."
          let ax ← collectAxioms name
          unless ax.all (#[``propext,``Classical.choice,``Quot.sound].contains ·) do
            throwError "native primary strain statement: nonstandard axioms {ax}"
          logInfo m!"PASS exact native full complex strain statement/56: {ax}"
        else
          save `native_node_strain_le_discrepancies params proof
            (app (root ++ `native_node_strain_le_discrepancies_statement) params)
            "The SAME original native primary node has full complex strain bounded by the sum of its exact original real and imaginary smooth discrepancies, with the dimension-only strain constant. Every geometric, source-admission, raw-identity and differentiability fact is instantiated. The selected application discharges the numerical frame tolerance (main:eq:lag-strain; main:eq:primary-strain)."


end JanetCartan.PhysicalPrimary.OriginalSelectedPrimaryStrain.StrainTransfer.NativeFinalTemplate
end

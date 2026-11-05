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
namespace JanetCartan.PhysicalPrimary.OriginalSelectedPrimaryStrain.StrainTransfer.NativeTensorTemplate
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

elab "retain_original_native_tensor_strain " mode:num : command => liftTermElabM do
  unless mode.getNat < 2 do throwError "native tensor strain: invalid mode"
  NativeContext.withSource fun c => do
    let p := c.params
    let n := mkApp (mkConst ``Nat.succ) p[0]!
    let dim := app `JanetCartan.embeddingDimension #[n]
    let body ← bodyAt c.tensorField
    let a := body.getAppArgs
    let H ← mkAppM ``Subtype.val #[c.tensor]
    let valueEq := app (root ++ `native_tensor_value) p
    let symmetry := app (helper `admitted_tensor_symmetry)
      #[n,dim,a[2]!,a[3]!,a[4]!,p[53]!,H,valueEq]
    let currentEq := app (root ++ `native_current_eq) p[:53].toArray
    let currentType ← equalityType currentEq
    let discrepancyEq := app (root ++ `native_discrepancy_eq) p
    let discrepancyType ← equalityType discrepancyEq
    unless currentType.isAppOfArity ``Eq 3 && discrepancyType.isAppOfArity ``Eq 3 do
      throwError "native tensor strain: checked original equalities changed"
    let graphBound := app (root ++ `graph_tensor_strain_le_discrepancy) c.graph
    let atFrame ← inferType graphBound
    unless atFrame.isForall do throwError "native tensor strain: original frame slot changed"
    withLocalDeclD `hFrameTolerance atFrame.bindingDomain! fun hGamma => do
      let bound := mkAppN graphBound #[hGamma,c.tensor,symmetry]
      forallBoundedTelescope (← inferType bound) (some 2) fun point _ => do
        unless point.size == 2 do throwError "native tensor strain: original point/core changed"
        let C := app `JanetCartan.UniformStep.projectedStressResidualConstant #[n,p[1]!]
        let B := app (response ++ `B) c.graph
        let proof := app (helper `tensor_error_bound_transport)
          #[n,dim,currentType.getAppArgs[1]!,currentType.getAppArgs[2]!,currentEq,B,H,
            discrepancyType.getAppArgs[2]!,discrepancyType.getAppArgs[1]!,discrepancyEq,
            point[0]!,C,mkAppN bound point]
        let params := p ++ #[hGamma] ++ point
        let statement := app (root ++ `native_tensor_strain_le_discrepancy_statement) params
        if mode.getNat == 0 then
          let type ← instantiateMVars (← mkForallFVars params (mkSort .zero))
          let value ← instantiateMVars (← mkLambdaFVars params (← inferType proof))
          for e in #[type,value] do
            if e.hasFVar || e.hasMVar || e.hasLevelMVar || e.hasLevelParam || e.hasLooseBVars || e.hasSorry then
              throwError "native tensor strain statement: unresolved actual input"
          let (type,value) := Lean.ShareCommon.shareCommon (type,value)
          let name := root ++ `native_tensor_strain_le_discrepancy_statement
          addDecl (.defnDecl {name,levelParams := [],type,value,hints := .regular 0,safety := .safe}) (forceExpose := true)
          addDocStringCore name "The exact original tensor/source-discrepancy inequality on the original core. This definition retains its statement, not its proof (main:eq:lag-strain)."
          logInfo m!"PASS exact original tensor strain statement/57: {← collectAxioms name}"
        else
          save `native_tensor_strain_le_discrepancy params proof statement
            "The actual original tensor quadrature is bounded by its SAME named source discrepancy under the original numerical frame tolerance. The checked original current/input identities and tensor-value equality are applied explicitly. The graph geometry, full PDE and uncut response are the originals (main:eq:lag-strain)."


end JanetCartan.PhysicalPrimary.OriginalSelectedPrimaryStrain.StrainTransfer.NativeTensorTemplate
end

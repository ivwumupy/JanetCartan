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
namespace JanetCartan.PhysicalPrimary.OriginalSelectedPrimaryStrain.StrainTransfer.NativeNormsTemplate
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

elab "retain_original_native_tensor_norms " mode:num : command => liftTermElabM do
  unless mode.getNat < 2 do throwError "native tensor norms: invalid mode"
  NativeContext.withSource fun c => do
    let p := c.params[:53].toArray
    let n := mkApp (mkConst ``Nat.succ) p[0]!
    let dim := app `JanetCartan.embeddingDimension #[n]
    let fixed := c.weak[:23].toArray
    let chi := app `JanetCartan.PhysicalInitialization.OriginalRegular.χ₂ fixed
    let sourceBody ← bodyAt c.tensorField
    let a := sourceBody.getAppArgs
    let F := a[2]!
    let chiFn := a[3]!
    let Zraw := a[4]!
    let B := app (response ++ `B) c.graph
    let realParams := p.push (mkConst ``Bool.false)
    let imaginaryParams := p.push (mkConst ``Bool.true)
    let tR := app (dataRoot ++ `tensor) realParams
    let tI := app (dataRoot ++ `tensor) imaginaryParams
    let HR ← mkAppM ``Subtype.val #[tR]
    let HI ← mkAppM ``Subtype.val #[tI]
    let source := app `JanetCartan.PhysicalPrimary.OriginalRawSourceField.source p
    let hRe ← mkAppM ``Eq.trans #[app (root ++ `native_tensor_value) realParams,
      app (helper `real_quadrature_eq) #[n,source]]
    let hIm ← mkAppM ``Eq.trans #[app (root ++ `native_tensor_value) imaginaryParams,
      app (helper `imaginary_quadrature_eq) #[n,source]]
    let identity := app (root ++ `native_corrected_identity) p
    let eq ← equalityType identity
    unless eq.isAppOfArity ``Eq 3 do throwError "native node norms: checked raw identity changed"
    let Z := eq.getAppArgs[1]!
    let corrected := eq.getAppArgs[2]!
    let differentiable := app (root ++ `native_raw_differentiable) p
    forallBoundedTelescope (← inferType differentiable) (some 2) fun point _ => do
      unless point.size == 2 do throwError "native node norms: original inner core changed"
      let x := point[0]!
      let hx := point[1]!
      let hχ ← termWith [(`chi,chi),(`x,x),(`hx,hx)]
        "chi.one_of_mem_closedBall (Metric.closedBall_subset_closedBall (half_le_self chi.rIn_pos.le) hx)"
      let hZ := mkAppN differentiable point
      let hR := app (root ++ `native_response_differentiable) (realParams ++ point)
      let hI := app (root ++ `native_response_differentiable) (imaginaryParams ++ point)
      let rawBound := app (helper `from_named_quadrature_norms)
        #[n,dim,F,chiFn,B,Zraw,HR,HI,hRe,hIm,x,hχ,hZ,hR,hI]
      let price := (← inferType rawBound).getAppArgs.back!
      let proof := app (helper `strain_bound_of_same_atom) #[n,dim,F,Z,corrected,identity,x,price,rawBound]
      let params := p ++ point
      let statement := app (root ++ `native_node_strain_le_tensor_errors_statement) params
      if mode.getNat == 0 then
        let type ← instantiateMVars (← mkForallFVars params (mkSort .zero))
        let value ← instantiateMVars (← mkLambdaFVars params (← inferType proof))
        for e in #[type,value] do
          if e.hasFVar || e.hasMVar || e.hasLevelMVar || e.hasLevelParam || e.hasLooseBVars || e.hasSorry then
            throwError "native tensor norm statement: unresolved actual input"
        let (type,value) := Lean.ShareCommon.shareCommon (type,value)
        let name := root ++ `native_node_strain_le_tensor_errors_statement
        addDecl (.defnDecl {name,levelParams := [],type,value,hints := .regular 0,safety := .safe}) (forceExpose := true)
        addDocStringCore name "The exact actual complex-node/two-tensor-residual norm inequality on the original core. This definition retains only its statement; its proof is supplied separately (main:eq:lag-strain)."
        logInfo m!"PASS exact original tensor norm statement/55: {← collectAxioms name}"
      else
        save `native_node_strain_le_tensor_errors params proof statement
          "The actual original complex primary strain is bounded by its two full tensor residual norms. The exact raw identity, tensor values and original raw/response differentiability are supplied by separately checked original-data lemmas. The negative corrected-atom sign is retained before taking norms (main:eq:lag-strain)."


end JanetCartan.PhysicalPrimary.OriginalSelectedPrimaryStrain.StrainTransfer.NativeNormsTemplate
end

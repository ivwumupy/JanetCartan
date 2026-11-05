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
namespace JanetCartan.PhysicalPrimary.OriginalSelectedPrimaryStrain.StrainTransfer.NativeApplicationTemplate
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

elab "derive_original_native_identity_statement " which:num : command => liftTermElabM do
  unless which.getNat < 2 do throwError "native identity statement: invalid mode"
  NativeContext.withSource fun c => do
    let p := c.params[:53].toArray
    let target ← if which.getNat == 0 then do
      let rawBody ← bodyAt c.tensorField
      mkEq (app `JanetCartan.PhysicalPrimary.OriginalFullResponse.F c.weak) rawBody.getAppArgs[2]!
    else do
      let eq ← inferType (app (raw ++ `combined_eq_corrected_raw) c.rawSmoothArgs)
      mkEq (app `JanetCartan.PhysicalPrimary.OriginalSampledPhysicalProfiles.selectedSourceCombinedWave p)
        eq.getAppArgs[2]!
    let key := if which.getNat == 0 then `native_current_eq_statement else `native_corrected_identity_statement
    let type ← instantiateMVars (← mkForallFVars p (mkSort .zero))
    let value ← instantiateMVars (← mkLambdaFVars p target)
    for e in #[type,value] do
      if e.hasFVar || e.hasMVar || e.hasLevelMVar || e.hasLevelParam || e.hasLooseBVars || e.hasSorry then
        throwError "native identity statement: unresolved actual data"
    let (type,value) := Lean.ShareCommon.shareCommon (type,value)
    let name := root ++ key
    addDecl (.defnDecl {name,levelParams := [],type,value,hints := .regular 0,safety := .safe}) (forceExpose := true)
    addDocStringCore name "The exact original-data equality to be proved in the native strain transfer. This definition only retains its statement; no equality proof is assumed (main:eq:lag-strain)."
    logInfo m!"PASS exact native identity statement {key}/53: {← collectAxioms name}"

elab "derive_original_native_current_identity_from_statement" : command => liftTermElabM do
  NativeContext.withSource fun c => do
    let p := c.params[:53].toArray
    let target := app (root ++ `native_current_eq_statement) p
    let eq ← bodyAt target
    let proof ← mkEqRefl eq.getAppArgs[2]!
    save `native_current_eq p proof target
      "The actual original graph current equals the raw source current, by its exact definitional identity. The separately checked equality statement adds no hypothesis (main:eq:lag-strain)."

elab "derive_original_native_corrected_identity" : command => liftTermElabM do
  NativeContext.withSource fun c => do
    let p := c.params[:53].toArray
    let proof := app (raw ++ `combined_eq_corrected_raw) c.rawSmoothArgs
    let eq ← inferType proof
    unless eq.isAppOfArity ``Eq 3 do throwError "native strain identity: original Eq changed"
    let node := app `JanetCartan.PhysicalPrimary.OriginalSampledPhysicalProfiles.selectedSourceCombinedWave p
    let target := app (root ++ `native_corrected_identity_statement) p
    unless node == (← bodyAt target).getAppArgs[1]! && eq.getAppArgs[2]! == (← bodyAt target).getAppArgs[2]! do
      throwError "native corrected identity: retained statement changed"
    save `native_corrected_identity p proof target
      "The SAME original primary node equals the full complex correction of its actual raw primary, using Native.combined_eq_corrected_raw on the original raw69/smooth70 operands. No cutoff or source is reselected (main:eq:lag-strain)."

elab "derive_original_native_tensor_strain_from_data" : command => liftTermElabM do
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
        save `native_tensor_strain_le_discrepancy (p ++ #[hGamma] ++ point) proof (← inferType proof)
          "The actual original tensor quadrature is bounded by its SAME named source discrepancy under the original numerical frame tolerance. The checked original current/input identities and tensor-value equality are applied explicitly. The graph geometry, full PDE and uncut response are the originals (main:eq:lag-strain)."

elab "derive_original_native_node_norms_from_data" : command => liftTermElabM do
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
      save `native_node_strain_le_tensor_errors (p ++ point) proof (← inferType proof)
        "The actual original complex primary strain is bounded by its two full tensor residual norms. The exact raw identity, tensor values and original raw/response differentiability are supplied by separately checked original-data lemmas. The negative corrected-atom sign is retained before taking norms (main:eq:lag-strain)."

elab "derive_original_native_primary_strain_from_data" : command => liftTermElabM do
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
      forallBoundedTelescope (← inferType triangle) (some 2) fun point target => do
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
        save `native_node_strain_le_discrepancies (p ++ #[hGamma] ++ point) proof (← inferType proof)
          "The SAME original native primary node has full complex strain bounded by the sum of its exact original real and imaginary smooth discrepancies, with the dimension-only strain constant. Every geometric, source-admission, raw-identity and differentiability fact is instantiated. The selected application discharges the numerical frame tolerance (main:eq:lag-strain; main:eq:primary-strain)."

end JanetCartan.PhysicalPrimary.OriginalSelectedPrimaryStrain.StrainTransfer.NativeApplicationTemplate
end

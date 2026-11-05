module

public import JanetCartan.Iteration.PhysicalMean.OriginalCanonicalBaselineTemplate
public import JanetCartan.Iteration.PhysicalMean.OriginalBackgroundHermitianTemplate
import all JanetCartan.Iteration.PhysicalMean.OriginalBackgroundHermitianTemplate
import all JanetCartan.Iteration.PhysicalMean.OriginalCanonicalDerivativeTemplate
public meta import Lean

/-!
# Apply the original full-response smoothness to the positive baseline

The saved actual60 response supplies full corrected-amplitude regularity. The
original full-parent geometry places the complete physical observation support
and every supported outer carrier in that response region. This gives the
positive baseline whether or not the inner incidence factor vanishes. No new
smoothness, inverse, scalar, rate, geometry-success or sample premise is added
(`app:ch_waves:eq:background-quadrature`). The smaller PDE source cutoff is not
identified with the common observation cutoff.
-/

public meta section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
namespace JanetCartan.PhysicalMean.OriginalCanonicalBaselineApplication
open Lean Meta Elab Command
open OriginalBackgroundHermitianTemplate

private def root := `JanetCartan.PhysicalMean.OriginalCanonicalBaseline
private def observation := `JanetCartan.PhysicalMean.OriginalCanonicalDerivative

private def save (name : Name) (params : Array Expr) (value : Expr)
    (data : Bool) (expected : Option Expr := none) : MetaM Expr := do
  let target ← match expected with | some t => pure t | none => inferType value
  let type ← instantiateMVars (← mkForallFVars params target)
  let value ← instantiateMVars (← mkLambdaFVars params value)
  let env ← getEnv
  for closed in #[type,value] do
    let missing := closed.getUsedConstants.filter (fun n => (env.find? n).isNone)
    unless missing.isEmpty do
      throwError "actual positive baseline: missing producer constants {missing.toList}"
  if type.hasFVar || type.hasMVar || type.hasLevelMVar || type.hasLooseBVars || type.hasSorry ||
      value.hasFVar || value.hasMVar || value.hasLevelMVar || value.hasLooseBVars || value.hasSorry then
    throwError "actual positive baseline: open or assumed field {name}"
  let name := root ++ name
  if data then
    addDecl (.defnDecl {name,levelParams := [],type,value,hints := .abbrev,safety := .safe}) (forceExpose := true)
  else
    addDecl (.thmDecl {name,levelParams := [],type,value}) (forceExpose := true)
  addDocStringCore name "The SAME unscaled positive corrected derivative amplitude on the original outer carrier support, with only the prescribed source observation for its auxiliary periodic extension. No inner factor or Fourier scalar (app:ch_waves:eq:background-quadrature)."
  return mkAppN (mkConst name) params

private def subsetArguments (type : Expr) : MetaM (Expr × Expr) := do
  if type.isAppOfArity ``LE.le 4 then
    return (type.getAppArgs[2]!,type.getAppArgs[3]!)
  if type.isAppOfArity ``Set.Subset 3 then
    return (type.getAppArgs[1]!,type.getAppArgs[2]!)
  throwError "actual positive baseline: changed literal subset producer"

private def withPositiveSlice
    (next : Array Expr → Array Expr → Expr → Expr → MetaM Unit) : MetaM Unit := do
  withTransparency .reducible <| withActualRow fun d => do
    let .forallE label colorType _ bi ← inferType d.native64[61]!
      | throwError "actual positive baseline: missing original color rate domain"
    withLocalDeclNoLocalInstanceUpdate label bi colorType fun color => do
      let actual ← savedResponse d color
      let hA := mkAppN (mkConst
        `JanetCartan.PhysicalPrimary.OriginalPhysicalResponse.derivative_smooth) actual.full60
      let n := d.raw13[0]!
      let N := d.raw13[1]!
      let A := mkApp (mkAppN (mkConst
        `JanetCartan.PhysicalMean.OriginalBackgroundHermitian.amplitude) d.parameters)
        (mkApp d.native64[61]! color)
      let bg (key : Name) := mkAppN (mkConst
        (`JanetCartan.PhysicalMean.OriginalBackgroundHermitian ++ key)) d.parameters
      let hP := mkApp (bg `parent_in_response_region) color
      let (P,Ω) ← subsetArguments (← inferType hP)
      let support ← mkAppM ``tsupport #[bg `ψ]
      withLocalDeclNoLocalInstanceUpdate `node .default
          (mkConst `JanetCartan.SeparatedSampling.Point) fun node => do
        withLocalDeclNoLocalInstanceUpdate `hOuter .default
            (← mkAppM ``Membership.mem #[support,node]) fun hOuter => do
          let coordinate ← nodeAt node
          let c ← mkAppM ``Prod.mk #[coordinate,mkApp (bg `ζ) coordinate]
          let graph := bg `graph_in_parent
          let hparent ← forallBoundedTelescope (← inferType graph) (some 2) fun xh _ => do
            unless xh.size == 2 do throwError "actual positive baseline: missing physical parent arguments"
            mkLambdaFVars xh (mkAppN graph (xh ++ #[node,hOuter]))
          let params := d.parameters ++ #[color,node,hOuter]
          unless params.size == 54 do throwError "actual positive baseline: changed native54"
          let original22 := d.native64[:22].toArray
          let obs (key : Name) := mkAppN (mkConst (observation ++ key)) original22
          let ψ := obs `observationFunction
          let hψ := obs `observation_smooth
          let hcell := obs `observation_cell
          let cellType ← inferType hcell
          unless cellType.isAppOfArity ``LT.lt 4 do
            throwError "actual positive baseline: changed observation cell bound"
          let b := cellType.getAppArgs[2]!
          let obsBody ← bodyAt (observation ++ `observationFunction) original22
          unless obsBody.getAppNumArgs == 3 do
            throwError "actual positive baseline: changed source observation spine"
          let hψX := mkAppN (mkConst
            `JanetCartan.PhysicalMean.OriginalCanonicalBaseline.sourceObservation_support_open)
            obsBody.getAppArgs
          let (_,X) ← subsetArguments (← inferType hψX)
          let hX ← mkAppOptM ``Metric.isOpen_ball (X.getAppArgs.map some)
          let sliceProof := mkAppN (mkConst
            `JanetCartan.PhysicalMean.OriginalCanonicalBaseline.parentAmplitude_slice_smooth)
            #[n,N,b,P,Ω,A,hA,c,hparent,hP]
          let sliceType ← inferType sliceProof
          let slice := sliceType.getAppArgs[sliceType.getAppNumArgs-2]!
          let hbox := mkAppN (mkConst
            ``JanetCartan.PhysicalMean.OriginalCanonicalDerivativeTemplate.source_cutoff_box)
            obsBody.getAppArgs
          let native := #[n,N,X,hX,slice,
            mkAppN (mkConst (root ++ `positiveSlice_smooth)) params,ψ,hψ,hψX,b,hcell,hbox]
          next params native sliceProof (mkApp (mkConst `JanetCartan.Torus) n)

elab "construct_actual_canonical_baseline " mode:num : command => liftTermElabM do
  withPositiveSlice fun params native sliceProof torus => do
    match mode.getNat with
    | 0 =>
      discard <| save `positiveSlice_smooth params sliceProof false
      logInfo "actual native54 positive amplitude: SAME original unscaled source and full B, original outer support, no inner-mask assumption"
    | 1 =>
      discard <| save `positiveBaseline params
        (mkAppN (mkConst `JanetCartan.PhysicalMean.OriginalCanonicalBaseline.observedBaseline) native) true
      logInfo "actual native54 positive baseline: SAME source observation only; no a, kappa, detector, Fourier scalar, or sample division"
    | 2 =>
      let value := mkAppN (mkConst `JanetCartan.PhysicalMean.OriginalCanonicalBaseline.observedBaseline) native
      let base := mkAppN (mkConst (root ++ `positiveBaseline)) params
      withLocalDeclNoLocalInstanceUpdate `z .default torus fun z => do
        let proof := mkAppN (mkConst
          `JanetCartan.PhysicalMean.OriginalCanonicalBaseline.observedBaseline_apply) (native.push z)
        let target := (← inferType proof).replace fun e => if e == value then some base else none
        discard <| save `positiveBaseline_native (params.push z) proof false (some target)
        logInfo "actual native55 positive baseline realization: literal unscaled full corrected derivative amplitude at the original carrier"
    | _ => throwError "actual positive baseline: unknown publication stage"

end JanetCartan.PhysicalMean.OriginalCanonicalBaselineApplication
end

module

public meta import JanetCartan.Iteration.PhysicalPrimary.OriginalSelectedPrimaryStrain.Node.StatementTemplate
public import JanetCartan.Iteration.PhysicalPrimary.OriginalSelectedPrimaryStrain.StrainTransfer.SelectedCore
public meta import JanetCartan.Iteration.PhysicalPrimary.OriginalSelectedPrimaryStrain.StrainTransfer.NativeContext
import all JanetCartan.Iteration.PhysicalPrimary.OriginalSelectedPrimaryStrain.Node.StatementTemplate
import all JanetCartan.Iteration.PhysicalPrimary.OriginalSelectedPrimaryStrain.StrainTransfer.SelectedStatement
import all JanetCartan.Iteration.PhysicalPrimary.OriginalSelectedPrimaryStrain.StrainTransfer.NativeFinalStatement
import all JanetCartan.Iteration.PhysicalPrimary.OriginalLocalWaves
import all JanetCartan.Iteration.PhysicalInitialization.CurrentLeading
import all JanetCartan.Iteration.PhysicalBackground.CanonicalDensity
import all JanetCartan.Iteration.PhysicalMean.OriginalCanonicalMomentAdmissionTemplate
import all JanetCartan.Iteration.PhysicalSampling.OriginalPositiveEventApplication
import all JanetCartan.Iteration.PhysicalSampling.OriginalNativeInitialEventApplication
import all JanetCartan.Iteration.PhysicalSampling.OriginalNativeGradedEventApplication
import all JanetCartan.Iteration.PhysicalSampling.OriginalNativeSourceRowsApplication
public meta import Lean

/-!
# The same complex strain tensor in the original node and selected transfer

Read the tensor inside the norm of the original finite-sampling node premise
and the tensor inside the selected two-discrepancy comparison. Retain their
exact equality using only selected52, the Picard count, sample, and point.
The auxiliary profile, accuracy, price and core admissions do not occur in
either tensor. Consumer: `NodeUniformTransfer`, which transports the selected
norm bound to the original aggregation premise (`main:eq:primary-strain`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true
set_option Elab.async false

public meta section
namespace JanetCartan.PhysicalPrimary.OriginalSelectedPrimaryStrain.Node.MetricIdentityTemplate

open Lean Meta Elab Command
open FamilyTemplate

private def nodeRoot :=
  `JanetCartan.PhysicalPrimary.OriginalSelectedPrimaryStrain.Node
private def transferRoot :=
  `JanetCartan.PhysicalPrimary.OriginalSelectedPrimaryStrain.StrainTransfer

def bodyAt (e : Expr) : MetaM Expr := do
  let ci ← getConstInfo e.getAppFn.constName!
  let some value := ci.value? (allowOpaque := true) |
    throwError "original node metric identity: unavailable saved body {ci.name}"
  return ((value.instantiateLevelParams ci.levelParams e.getAppFn.constLevels!).beta
    e.getAppArgs).headBeta

private def selectedInequality (e : Expr) : MetaM Expr := do
  let mut result := e
  for key in #[transferRoot ++ `selected_node_strain_le_discrepancies_statement,
      transferRoot ++ `native_node_strain_le_discrepancies_statement] do
    unless result.isAppOfArity key 56 do
      throwError "original node metric identity: selected/native statement changed"
    result ← bodyAt result
  return result

/-- Extract both actual norm tensors with arbitrary accuracy and nonnegative
price. Their exact equality must close without these temporary variables or
either independently typed core admission. -/
def withTensors (next : Array Expr → Array Expr → Expr → Expr → Expr → MetaM Unit) : MetaM Unit :=
  DataTemplate.withData fun d =>
    withLocalDeclNoLocalInstanceUpdate `accuracy .default (mkConst ``Nat) fun q =>
      withLocalDeclNoLocalInstanceUpdate `C .default (mkConst ``Real) fun C => do
        let hCType ← mkAppM ``LE.le #[← mkNumeral (mkConst ``Real) 0,C]
        withLocalDeclNoLocalInstanceUpdate `hC .default hCType fun hC => do
          let proposed ← NodeStatementTemplate.requirement d q C hC
          let .forallE xName xType xBody xBi := (← whnf proposed).consumeMData |
            throwError "original node metric identity: original point binder changed"
          withLocalDeclNoLocalInstanceUpdate xName xBi xType fun x => do
            let .forallE hxName hxType hxBody hxBi :=
                (← whnf (xBody.instantiate1 x)).consumeMData |
              throwError "original node metric identity: original core binder changed"
            withLocalDeclNoLocalInstanceUpdate hxName hxBi hxType fun hx => do
              let original := hxBody.instantiate1 hx
              let comparison ← resultAt (transferRoot ++ `selected_node_strain_le_discrepancies) d.args
              let .forallE _ txType txBody _ := comparison.consumeMData |
                throwError "original node metric identity: selected point binder changed"
              unless ← isDefEq txType xType do
                throwError "original node metric identity: different point type"
              let .forallE thxName thxType thxBody thxBi := (txBody.instantiate1 x).consumeMData |
                throwError "original node metric identity: selected core binder changed"
              withLocalDeclNoLocalInstanceUpdate thxName thxBi thxType fun thx => do
                let selected ← selectedInequality (thxBody.instantiate1 thx)
                unless original.isAppOfArity ``LE.le 4 && selected.isAppOfArity ``LE.le 4 do
                  throwError "original node metric identity: original inequalities changed"
                let leftNorm := original.getAppArgs[2]!
                let rightNorm := selected.getAppArgs[2]!
                unless leftNorm.isAppOfArity ``Norm.norm 3 && rightNorm.isAppOfArity ``Norm.norm 3 do
                  throwError "original node metric identity: not the two original tensor norms"
                let alpha := leftNorm.getAppArgs[0]!
                let left := leftNorm.getAppArgs[2]!
                let right := rightNorm.getAppArgs[2]!
                unless left.isAppOfArity ``JanetCartan.WKB.complexLinearizedMetric 5 &&
                    right.isAppOfArity ``JanetCartan.WKB.complexLinearizedMetric 5 do
                  throwError "original node metric identity: original complex strain tensors changed"
                let p := d.args.push x
                unless p.size == 55 do
                  throwError "original node metric identity: selected52/N/sample/point changed"
                let equality := mkAppN (mkConst ``Eq [.succ .zero]) #[alpha,left,right]
                let closed ← mkLambdaFVars p equality
                if closed.hasFVar || closed.hasLooseBVars then
                  throwError "original node metric identity: auxiliary profile, accuracy, price or core admission escaped"
                next p (d.sourceArgs.push x) alpha left right

/-- Read the same original aggregate premise before the selected Picard source
is substituted. This is the native-source version of
`NodeStatementTemplate.requirement`; its amplitude again disappears. -/
private def nativeRequirement (sourceArgs : Array Expr) (q C hC : Expr) : MetaM Expr :=
  withLocalDeclNoLocalInstanceUpdate `δ .default (mkConst ``Real) fun δ => do
    let hδType ← mkAppM ``LE.le #[← mkNumeral (mkConst ``Real) 0,δ]
    withLocalDeclNoLocalInstanceUpdate `hδ .default hδType fun hδ => do
      let source := sourceArgs[:52].toArray
      let args := source[:44].toArray ++ #[C,hC,q] ++ source[44:].toArray ++ #[δ,hδ]
      let type ← resultAt
        `JanetCartan.PhysicalPrimary.OriginalSampledPhysicalProfiles.selectedSourcePrimary_strain_of_complex_strain args
      let .forallE _ nodeType _ _ := type.consumeMData |
        throwError "original native node metric identity: aggregate premise changed"
      let .forallE _ sampleType body _ := (← whnf nodeType).consumeMData |
        throwError "original native node metric identity: sample binder changed"
      unless ← isDefEq sampleType (← inferType sourceArgs[52]!) do
        throwError "original native node metric identity: different original sample"
      let target := body.instantiate1 sourceArgs[52]!
      if (target.find? (fun e => e == δ || e == hδ)).isSome then
        throwError "original native node metric identity: amplitude escaped"
      return target

/-- The literal tensor equality at sourceArgs53,x. The numerical frame bound
and the two core admissions are used only to read the checked comparison;
none may occur in the retained tensors or their parameter types. -/
def withNativeTensors (next : Array Expr → Expr → Expr → Expr → MetaM Unit) : MetaM Unit :=
  StrainTransfer.NativeContext.withSource fun c => do
    let sourceArgs := c.params[:53].toArray
    withLocalDeclNoLocalInstanceUpdate `accuracy .default (mkConst ``Nat) fun q =>
      withLocalDeclNoLocalInstanceUpdate `C .default (mkConst ``Real) fun C => do
        let hCType ← mkAppM ``LE.le #[← mkNumeral (mkConst ``Real) 0,C]
        withLocalDeclNoLocalInstanceUpdate `hC .default hCType fun hC => do
          let proposed ← nativeRequirement sourceArgs q C hC
          let .forallE xName xType xBody xBi := (← whnf proposed).consumeMData |
            throwError "original native node metric identity: original point binder changed"
          withLocalDeclNoLocalInstanceUpdate xName xBi xType fun x => do
            let .forallE hxName hxType hxBody hxBi :=
                (← whnf (xBody.instantiate1 x)).consumeMData |
              throwError "original native node metric identity: original core binder changed"
            withLocalDeclNoLocalInstanceUpdate hxName hxBi hxType fun hx => do
              let original := hxBody.instantiate1 hx
              let comparison ← resultAt (transferRoot ++ `native_node_strain_le_discrepancies) sourceArgs
              let .forallE frameName frameType frameBody frameBi := comparison.consumeMData |
                throwError "original native node metric identity: numerical frame binder changed"
              withLocalDeclNoLocalInstanceUpdate frameName frameBi frameType fun frame => do
                let .forallE _ txType txBody _ := (frameBody.instantiate1 frame).consumeMData |
                  throwError "original native node metric identity: native point binder changed"
                unless ← isDefEq txType xType do
                  throwError "original native node metric identity: different point type"
                let .forallE thxName thxType thxBody thxBi := (txBody.instantiate1 x).consumeMData |
                  throwError "original native node metric identity: native core binder changed"
                withLocalDeclNoLocalInstanceUpdate thxName thxBi thxType fun thx => do
                  let saved := thxBody.instantiate1 thx
                  unless saved.isAppOfArity (transferRoot ++ `native_node_strain_le_discrepancies_statement) 56 do
                    throwError "original native node metric identity: native statement changed"
                  let native ← bodyAt saved
                  unless original.isAppOfArity ``LE.le 4 && native.isAppOfArity ``LE.le 4 do
                    throwError "original native node metric identity: inequalities changed"
                  let leftNorm := original.getAppArgs[2]!
                  let rightNorm := native.getAppArgs[2]!
                  unless leftNorm.isAppOfArity ``Norm.norm 3 && rightNorm.isAppOfArity ``Norm.norm 3 do
                    throwError "original native node metric identity: tensor norms changed"
                  let alpha := leftNorm.getAppArgs[0]!
                  let left := leftNorm.getAppArgs[2]!
                  let right := rightNorm.getAppArgs[2]!
                  unless left.isAppOfArity ``JanetCartan.WKB.complexLinearizedMetric 5 &&
                      right.isAppOfArity ``JanetCartan.WKB.complexLinearizedMetric 5 do
                    throwError "original native node metric identity: complex tensors changed"
                  let p := sourceArgs.push x
                  let equality := mkAppN (mkConst ``Eq [.succ .zero]) #[alpha,left,right]
                  let closed ← mkLambdaFVars p equality
                  unless p.size == 54 && !closed.hasFVar && !closed.hasLooseBVars do
                    throwError "original native node metric identity: an accuracy, price, frame or core premise escaped"
                  next p alpha left right

private def openRaw (count : Nat) (type : Expr)
    (next : Array Expr → MetaM Unit) : MetaM Unit := loop count type #[]
where
  loop : Nat → Expr → Array Expr → MetaM Unit
    | 0,_,p => next p
    | k+1,type,p => do
      let .forallE name domain body bi := type.consumeMData |
        throwError "original node metric identity: retained telescope ended at {p.size}"
      let domain := domain.instantiateRev p
      if bi == .instImplicit then
        withLocalDecl name bi domain fun x => loop k body (p.push x)
      else
        withLocalDeclNoLocalInstanceUpdate name bi domain fun x => loop k body (p.push x)

private def save (key : Name) (p : Array Expr) (proof target : Expr)
    (data : Bool) : MetaM Unit := do
  let type ← instantiateMVars (← mkForallFVars p target)
  let value ← instantiateMVars (← mkLambdaFVars p proof)
  let env ← getEnv
  for e in #[type,value] do
    if e.hasFVar || e.hasMVar || e.hasLevelMVar || e.hasLevelParam ||
        e.hasLooseBVars || e.hasSorry then
      throwError "original node metric identity: unresolved or additional input in {key}"
    let missing := e.getUsedConstants.filter fun name => (env.find? name).isNone
    unless missing.isEmpty do
      throwError "original node metric identity: missing original metadata {missing}"
    if e.getUsedConstants.any (fun name => name.toString.startsWith "Scratch." ||
        name.toString.startsWith "GoalNodeMetricIdentity" || name.toString.startsWith "JanetCartan.Scratch.") then
      throwError "original node metric identity: forbidden scratch dependency"
  let name := nodeRoot ++ key
  if (env.find? name).isSome then throwError "original node metric identity: duplicate {name}"
  let (type,value) := Lean.ShareCommon.shareCommon (type,value)
  IO.println s!"Kernel checking original node complex metric {key}/{p.size}"
  (← IO.getStdout).flush
  if data then
    addDecl (.defnDecl {name,levelParams := [],type,value,hints := .regular 0,safety := .safe})
      (forceExpose := true)
  else
    addDecl (.thmDecl {name,levelParams := [],type,value}) (forceExpose := true)
  addDocStringCore name "The exact complex strain tensor inside the original selectedSourcePrimary_strain_of_complex_strain node-premise norm equals the tensor inside the original source-discrepancy comparison. The native cache uses sourceArgs53,x; its selected specialization uses exactly selected52,N,sample,x. No auxiliary profile, operator reach, accuracy, price, source-decay bound or core admission is added. Consumer: NodeUniformTransfer (main:eq:primary-strain)."
  let axioms ← collectAxioms name
  unless axioms.all (#[``propext,``Classical.choice,``Quot.sound].contains ·) do
    throwError "original node metric identity: nonstandard axioms {axioms}"
  logInfo m!"PASS original node complex metric {key}/{p.size}: {axioms}"

elab "retain_original_native_node_metric_statement" : command => liftTermElabM do
  withNativeTensors fun p alpha left right => do
    let equality := mkAppN (mkConst ``Eq [.succ .zero]) #[alpha,left,right]
    save `native_metric_tensor_eq_statement p equality (mkSort .zero) true

elab "retain_original_node_metric_statement" : command => liftTermElabM do
  withTensors fun p native alpha left right => do
    let equality := mkAppN (mkConst ``Eq [.succ .zero]) #[alpha,left,right]
    let nativeStatement := app (nodeRoot ++ `native_metric_tensor_eq_statement) native
    unless (← bodyAt nativeStatement) == equality do
      throwError "original node metric identity: native specialization changed either exact selected tensor"
    save `metric_tensor_eq_statement p nativeStatement (mkSort .zero) true

elab "prove_original_native_node_metric_identity" : command => liftTermElabM do
  let statementName := nodeRoot ++ `native_metric_tensor_eq_statement
  openRaw 54 (← getConstInfo statementName).type fun p => do
    let target := app statementName p
    let equality ← bodyAt target
    unless equality.isAppOfArity ``Eq 3 do
      throwError "original node metric identity: retained equality changed"
    let a := equality.getAppArgs
    let left := a[1]!
    let right := a[2]!
    unless left.isAppOfArity ``JanetCartan.WKB.complexLinearizedMetric 5 &&
        right.isAppOfArity ``JanetCartan.WKB.complexLinearizedMetric 5 do
      throwError "original node metric identity: retained complex tensors changed"
    let la := left.getAppArgs
    let ra := right.getAppArgs
    unless ra[2]!.isAppOfArity `JanetCartan.PhysicalPrimary.OriginalLocalWaves.F 53 do
      throwError "original node metric identity: raw-current definition changed"
    let history ← bodyAt ra[2]!
    unless history.isAppOfArity `JanetCartan.PhysicalInitialization.CurrentLeading.History.F 37 do
      throwError "original node metric identity: raw-history definition changed"
    let finite ← bodyAt history
    let common := mkAppN left.getAppFn (la.set! 3 la[3]!.headBeta)
    let normalizedRight := mkAppN right.getAppFn ((ra.set! 2 finite).set! 3 ra[3]!.headBeta)
    unless common == normalizedRight do
      throwError "original node metric identity: the saved current and node definitions do not give the SAME tensor"
    let proof := mkAppN (mkConst ``Eq.refl equality.getAppFn.constLevels!) #[a[0]!,common]
    save `native_metric_tensor_eq p proof target false

elab "prove_original_node_metric_identity" : command => liftTermElabM do
  let statementName := nodeRoot ++ `metric_tensor_eq_statement
  openRaw 55 (← getConstInfo statementName).type fun p => do
    let target := app statementName p
    let nativeStatement ← bodyAt target
    unless nativeStatement.isAppOfArity (nodeRoot ++ `native_metric_tensor_eq_statement) 54 do
      throwError "original node metric identity: native specialization changed"
    let proof := app (nodeRoot ++ `native_metric_tensor_eq) nativeStatement.getAppArgs
    save `metric_tensor_eq p proof target false

end JanetCartan.PhysicalPrimary.OriginalSelectedPrimaryStrain.Node.MetricIdentityTemplate
end

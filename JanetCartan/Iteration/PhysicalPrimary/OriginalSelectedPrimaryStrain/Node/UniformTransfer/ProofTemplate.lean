module

public import JanetCartan.Iteration.PhysicalPrimary.OriginalSelectedPrimaryStrain.Node.UniformTransfer.Basic
public meta import JanetCartan.Iteration.PhysicalPrimary.OriginalSelectedPrimaryStrain.Node.UniformTransfer.Template
import all JanetCartan.Iteration.PhysicalPrimary.OriginalSelectedPrimaryStrain.Node.UniformTransfer.Template
public meta import JanetCartan.Iteration.PhysicalPrimary.OriginalSelectedPrimaryStrain.Node.StatementTemplate
import all JanetCartan.Iteration.PhysicalBackground.CanonicalDensity
import all JanetCartan.Iteration.PhysicalMean.OriginalCanonicalMomentAdmissionTemplate
import all JanetCartan.Iteration.PhysicalSampling.OriginalPositiveEventApplication
import all JanetCartan.Iteration.PhysicalSampling.OriginalNativeInitialEventApplication
import all JanetCartan.Iteration.PhysicalSampling.OriginalNativeGradedEventApplication
import all JanetCartan.Iteration.PhysicalSampling.OriginalNativeSourceRowsApplication

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true
set_option Elab.async false
open scoped ContDiff Matrix.Norms.Frobenius JanetCartan.TensorFrobenius

/-! Apply the two admitted-label identities before summing the source
bounds, and return the original finite-sampling aggregation premise. The
nonnegative price and the single full-family pointwise bound are the only
analytic inputs (`main:eq:primary-strain`). -/

public meta section
namespace JanetCartan.PhysicalPrimary.OriginalSelectedPrimaryStrain.NodeUniformTransfer.ProofTemplate
open Lean Meta
open JanetCartan.PhysicalPrimary.OriginalSelectedPrimaryStrain
open NodeUniformTransfer.Template

/-- Transport membership along the published original smoothing-core equality. -/
def originalCoreMembership (point : Array Expr) : MetaM Expr := do
  let membership ← inferType point[1]!
  unless membership.isAppOfArity ``Membership.mem 5 do
    throwError "node uniform transfer: original core membership changed"
  let core := membership.getAppArgs[3]!
  unless core.isAppOfArity ``JanetCartan.LocalDomain.core 2 do
    throwError "node uniform transfer: not the original aggregate core"
  let domain := core.getAppArgs[0]!
  unless domain.isAppOfArity `JanetCartan.RevisedUniform.OriginalSmoothing.Dsmooth 23 do
    throwError "node uniform transfer: not the SAME original smoothing domain"
  let equality := app `JanetCartan.PhysicalPrimary.OriginalLocalWaveGeometry.same_core domain.getAppArgs
  let eq ← inferType equality
  unless eq.isAppOfArity ``Eq 3 && eq.getAppArgs[1]! == core do
    throwError "node uniform transfer: original core equality has different operands"
  let predicate ← withLocalDeclNoLocalInstanceUpdate `s .default eq.getAppArgs[0]! fun s => do
    let prop := mkAppN membership.getAppFn (membership.getAppArgs.set! 3 s)
    mkLambdaFVars #[s] prop
  let pointEquality ← mkAppM ``congrArg #[predicate,equality]
  mkAppM ``Eq.mp #[pointEquality,point[1]!]

/-- Use the exact source and carrier identities for this admitted quadrature. -/
def normalizedBound (d : RawProfilesTemplate.Data) (hOp q C hUniform : Expr)
    (point : Array Expr) (quad : Expr) : MetaM Expr := do
  let p := d.profileArgs ++ #[quad,hOp]
  let familyBound := mkAppN hUniform (#[labelAt d quad hOp] ++ point)
  let sourceEq := app (root ++ `admitted_discrepancy_eq) p
  let frequencyEq := app (root ++ `admitted_frequency_eq) p
  let proof ← mkAppM (root ++ `point_bound_of_eq)
    #[sourceEq,frequencyEq,q,point[0]!,familyBound]
  let type ← inferType proof
  unless type.isAppOfArity ``LE.le 4 do
    throwError "node uniform transfer: admitted bound is not a real inequality"
  let norm := type.getAppArgs[2]!
  unless norm.isAppOfArity ``Norm.norm 3 do
    throwError "node uniform transfer: admitted bound lost the source norm"
  let source := mkApp (app (sourceRoot ++ `discrepancy) (d.sourceArgs.push quad)) point[0]!
  unless norm.getAppArgs[2]! == source do
    throwError "node uniform transfer: admitted bound changed the actual source"
  let price ← mkAppM ``HMul.hMul #[C,← decayAt (← rhoAt d) q]
  unless type.getAppArgs[3]! == price do
    throwError "node uniform transfer: admitted bound changed the undoubled original carrier"
  return proof

/-- Assemble the exact node bound under its separately proved all-point tensor identity. -/
def publishConditional : MetaM Unit := do
  withOperator fun d hOp =>
    withLocalDeclNoLocalInstanceUpdate `accuracy .default (mkConst ``Nat) fun q =>
      withLocalDeclNoLocalInstanceUpdate `C .default (mkConst ``Real) fun C => do
        let nonneg ← mkAppM ``LE.le #[← mkNumeral (mkConst ``Real) 0,C]
        withLocalDeclNoLocalInstanceUpdate `hC .default nonneg fun hC => do
          let uniform := app (root ++ `uniform_discrepancy_bound) (d.fixed ++ #[q,C])
          withLocalDeclNoLocalInstanceUpdate `hDiscrepancy .default uniform fun hUniform => do
            let n := mkApp (mkConst ``Nat.succ) d.native[0]!
            let S := app ``JanetCartan.UniformStep.projectedStressResidualConstant #[n,d.native[1]!]
            let hS ← mkAppM ``le_of_lt
              #[app ``JanetCartan.UniformStep.projectedStressResidualConstant_pos #[n,d.native[1]!]]
            let statementArgs := d.args ++ #[q,C]
            let statement := app (root ++ `node_strain_statement) statementArgs
            let target ← bodyAt statement
            let .forallE _ space _ _ := (← whnf target).consumeMData |
              throwError "node uniform transfer: original point space changed"
            let metricType ← withLocalDeclNoLocalInstanceUpdate `x .default space fun x =>
              mkForallFVars #[x] (app (primaryRoot ++ `Node.native_metric_tensor_eq_statement)
                (d.sourceArgs.push x))
            withLocalDeclNoLocalInstanceUpdate `hMetric .default metricType fun hMetric => do
              let comparison := app (transferRoot ++ `selected_node_strain_le_discrepancies) d.args
              forallBoundedTelescope target (some 2) fun point expected => do
                unless point.size == 2 && expected.isAppOfArity ``LE.le 4 do
                  throwError "node uniform transfer: original node premise changed"
                let originalPoint := #[point[0]!,← originalCoreMembership point]
                let he := mkAppN comparison originalPoint
                let ha ← normalizedBound d hOp q C hUniform originalPoint (mkConst ``Bool.false)
                let hb ← normalizedBound d hOp q C hUniform originalPoint (mkConst ``Bool.true)
                let ta ← inferType ha
                let tb ← inferType hb
                let te ← selectedInequality (← inferType he)
                let decay ← decayAt (← rhoAt d) q
                let selectedBound := app ``both_quadrature_bounds
                  #[te.getAppArgs[2]!,ta.getAppArgs[2]!,tb.getAppArgs[2]!,S,C,decay,hS,he,ha,hb]
                let tensorEq := mkApp hMetric point[0]!
                let tensorStatement ← inferType tensorEq
                unless tensorStatement.isAppOfArity
                    (primaryRoot ++ `Node.native_metric_tensor_eq_statement) 54 do
                  throwError "node uniform transfer: exact native tensor statement changed"
                let tensorEqType ← bodyAt tensorStatement
                unless tensorEqType.isAppOfArity ``Eq 3 do
                  throwError "node uniform transfer: original node tensor identity changed"
                let aggregateNorm := expected.getAppArgs[2]!
                let selectedNorm := te.getAppArgs[2]!
                unless aggregateNorm.isAppOfArity ``Norm.norm 3 &&
                    selectedNorm.isAppOfArity ``Norm.norm 3 &&
                    tensorEqType.getAppArgs[1]! == aggregateNorm.getAppArgs[2]! &&
                    tensorEqType.getAppArgs[2]! == selectedNorm.getAppArgs[2]! do
                  throwError "node uniform transfer: different aggregate or selected tensor"
                let normFn ← withLocalDeclNoLocalInstanceUpdate `tensor .default
                    tensorEqType.getAppArgs[0]! fun tensor => do
                  let value := mkAppN selectedNorm.getAppFn
                    (selectedNorm.getAppArgs.set! 2 tensor)
                  mkLambdaFVars #[tensor] value
                let normEq ← mkAppM ``congrArg #[normFn,tensorEq]
                let proof ← mkAppM ``le_of_eq_of_le #[normEq,selectedBound]
                let p := d.fixed ++ #[q,C,hC,hUniform] ++ d.selected[33:].toArray ++
                  #[d.hAux,hOp,d.sample,hMetric]
                unless p.size == 61 && statementArgs.size == 56 do
                  throwError "node uniform transfer: extra data or analytic input entered"
                save `node_of_uniform_discrepancy_with_metric p (← mkLambdaFVars point proof) statement false

/-- Discharge the internal exact tensor identity using its original-data producer. -/
def publishFinal : MetaM Unit := do
  let conditionalName := root ++ `node_of_uniform_discrepancy_with_metric
  openRaw 60 (← getConstInfo conditionalName).type fun p => do
    let selected := p[:33].toArray ++ p[38:57].toArray
    let data := selected ++ #[p[33]!,p[59]!]
    unless selected.size == 52 && data.size == 54 do
      throwError "node uniform transfer: original final selected data boundary changed"
    let conditional := app conditionalName p
    let .forallE _ _ result _ := (← inferType conditional).consumeMData |
      throwError "node uniform transfer: internal tensor premise disappeared"
    let actualMetric := app (primaryRoot ++ `Node.metric_tensor_eq) data
    let target := result.instantiate1 actualMetric
    unless target == app (root ++ `node_strain_statement) (data ++ #[p[34]!,p[35]!]) do
      throwError "node uniform transfer: final exact compact result changed"
    save `node_of_uniform_discrepancy p (mkApp conditional actualMetric) target false

end JanetCartan.PhysicalPrimary.OriginalSelectedPrimaryStrain.NodeUniformTransfer.ProofTemplate
end

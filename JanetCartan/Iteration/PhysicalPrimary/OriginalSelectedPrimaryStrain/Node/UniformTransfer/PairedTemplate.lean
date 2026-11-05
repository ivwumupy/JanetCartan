module

public import JanetCartan.Iteration.PhysicalPrimary.OriginalSelectedPrimaryStrain.Node.UniformTransfer.Uniform
public import JanetCartan.Iteration.PhysicalPrimary.OriginalSelectedPrimaryStrain.Node.UniformTransfer.Statement
public import JanetCartan.Iteration.PhysicalPrimary.OriginalSelectedPrimaryStrain.Node.UniformTransfer.SourceIdentity
public import JanetCartan.Iteration.PhysicalPrimary.OriginalSelectedPrimaryStrain.Node.UniformTransfer.FrequencyIdentity

public meta import JanetCartan.Iteration.PhysicalPrimary.OriginalSelectedPrimaryStrain.Node.UniformTransfer.ProofTemplate
import all JanetCartan.Iteration.PhysicalPrimary.OriginalSelectedPrimaryStrain.Node.UniformTransfer.Template
import all JanetCartan.Iteration.PhysicalPrimary.OriginalSelectedPrimaryStrain.Node.UniformTransfer.Uniform
import all JanetCartan.Iteration.PhysicalPrimary.OriginalSelectedPrimaryStrain.Node.UniformTransfer.Statement
import all JanetCartan.Iteration.PhysicalPrimary.OriginalSelectedPrimaryStrain.Node.UniformTransfer.SourceStatement
import all JanetCartan.Iteration.PhysicalPrimary.OriginalSelectedPrimaryStrain.Node.UniformTransfer.FrequencyStatement
import all JanetCartan.Iteration.PhysicalPrimary.OriginalSelectedPrimaryStrain.StrainTransfer.SelectedStatement
import all JanetCartan.Iteration.PhysicalPrimary.OriginalSelectedPrimaryStrain.StrainTransfer.NativeFinalStatement
import all JanetCartan.Iteration.PhysicalBackground.CanonicalDensity
import all JanetCartan.Iteration.PhysicalMean.OriginalCanonicalMomentAdmissionTemplate
import all JanetCartan.Iteration.PhysicalSampling.OriginalPositiveEventApplication
import all JanetCartan.Iteration.PhysicalSampling.OriginalNativeInitialEventApplication
import all JanetCartan.Iteration.PhysicalSampling.OriginalNativeGradedEventApplication
import all JanetCartan.Iteration.PhysicalSampling.OriginalNativeSourceRowsApplication

/-! The original complex-node estimate from its two pointwise source
bounds. The large observed-family premise is absent from this tensor/norm
composition (`main:eq:primary-strain`). -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true
set_option Elab.async false
open scoped ContDiff Matrix.Norms.Frobenius JanetCartan.TensorFrobenius

public meta section
namespace JanetCartan.PhysicalPrimary.OriginalSelectedPrimaryStrain.NodeUniformTransfer.PairedTemplate
open Lean Meta
open JanetCartan.PhysicalPrimary.OriginalSelectedPrimaryStrain
open NodeUniformTransfer.Template

/-- The paired input is exactly the same original Pointwise statement for each Bool. -/
def publishStatement : MetaM Unit := do
  DataTemplate.withData fun d =>
    withLocalDeclNoLocalInstanceUpdate `accuracy .default (mkConst ``Nat) fun q =>
      withLocalDeclNoLocalInstanceUpdate `C .default (mkConst ``Real) fun C =>
        withLocalDeclNoLocalInstanceUpdate `imaginary .default (mkConst ``Bool) fun quad => do
          let source := app (root ++ `admitted_discrepancy_bound_statement)
            (d.args ++ #[quad,q,C])
          save `paired_discrepancy_bound (d.args ++ #[q,C])
            (← mkForallFVars #[quad] source) (mkSort .zero) true

/-- Apply the selected strain comparison and the actual native tensor identity. -/
def publishProof : MetaM Unit := do
  DataTemplate.withData fun d =>
    withLocalDeclNoLocalInstanceUpdate `accuracy .default (mkConst ``Nat) fun q =>
      withLocalDeclNoLocalInstanceUpdate `C .default (mkConst ``Real) fun C => do
        let nonneg ← mkAppM ``LE.le #[← mkNumeral (mkConst ``Real) 0,C]
        withLocalDeclNoLocalInstanceUpdate `hC .default nonneg fun hC => do
          let paired := app (root ++ `paired_discrepancy_bound) (d.args ++ #[q,C])
          withLocalDeclNoLocalInstanceUpdate `hPaired .default paired fun hPaired => do
            let statement := app (root ++ `node_strain_statement) (d.args ++ #[q,C])
            let target ← bodyAt statement
            let n := mkApp (mkConst ``Nat.succ) d.native[0]!
            let S := app ``JanetCartan.UniformStep.projectedStressResidualConstant #[n,d.native[1]!]
            let hS ← mkAppM ``le_of_lt
              #[app ``JanetCartan.UniformStep.projectedStressResidualConstant_pos #[n,d.native[1]!]]
            let comparison := app (transferRoot ++ `selected_node_strain_le_discrepancies) d.args
            forallBoundedTelescope target (some 2) fun point expected => do
              unless point.size == 2 && expected.isAppOfArity ``LE.le 4 do
                throwError "paired node transfer: original aggregation premise changed"
              let originalPoint := #[point[0]!,← ProofTemplate.originalCoreMembership point]
              let he := mkAppN comparison originalPoint
              let ha := mkAppN hPaired (#[mkConst ``Bool.false] ++ originalPoint)
              let hb := mkAppN hPaired (#[mkConst ``Bool.true] ++ originalPoint)
              let ta ← inferType ha
              let tb ← inferType hb
              unless ta.isAppOfArity ``LE.le 4 && tb.isAppOfArity ``LE.le 4 do
                throwError "paired node transfer: the exact source bounds changed"
              let te ← selectedInequality (← inferType he)
              let decay ← decayAt (← rhoAt d) q
              let selectedBound := app ``both_quadrature_bounds
                #[te.getAppArgs[2]!,ta.getAppArgs[2]!,tb.getAppArgs[2]!,S,C,decay,hS,he,ha,hb]
              let tensorEq := app (primaryRoot ++ `Node.native_metric_tensor_eq)
                (d.sourceArgs.push point[0]!)
              let tensorStatement ← inferType tensorEq
              unless tensorStatement.isAppOfArity
                  (primaryRoot ++ `Node.native_metric_tensor_eq_statement) 54 do
                throwError "paired node transfer: exact native tensor statement changed"
              let tensorEqType ← bodyAt tensorStatement
              unless tensorEqType.isAppOfArity ``Eq 3 do
                throwError "paired node transfer: native tensor equality changed"
              let aggregateNorm := expected.getAppArgs[2]!
              let selectedNorm := te.getAppArgs[2]!
              unless aggregateNorm.isAppOfArity ``Norm.norm 3 &&
                  selectedNorm.isAppOfArity ``Norm.norm 3 &&
                  tensorEqType.getAppArgs[1]! == aggregateNorm.getAppArgs[2]! &&
                  tensorEqType.getAppArgs[2]! == selectedNorm.getAppArgs[2]! do
                throwError "paired node transfer: different aggregate or selected tensor"
              let normFn ← withLocalDeclNoLocalInstanceUpdate `tensor .default
                  tensorEqType.getAppArgs[0]! fun tensor => do
                let value := mkAppN selectedNorm.getAppFn
                  (selectedNorm.getAppArgs.set! 2 tensor)
                mkLambdaFVars #[tensor] value
              let normEq ← mkAppM ``congrArg #[normFn,tensorEq]
              let proof ← mkAppM ``le_of_eq_of_le #[normEq,selectedBound]
              let p := d.args ++ #[q,C,hC,hPaired]
              unless p.size == 58 do
                throwError "paired node transfer: additional family data or analytic premise entered"
              save `node_of_paired_discrepancy p (← mkLambdaFVars point proof) statement false

end JanetCartan.PhysicalPrimary.OriginalSelectedPrimaryStrain.NodeUniformTransfer.PairedTemplate
end

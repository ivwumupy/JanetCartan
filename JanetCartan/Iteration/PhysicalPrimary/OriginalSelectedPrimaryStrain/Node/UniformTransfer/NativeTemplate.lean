module

public meta import JanetCartan.Iteration.PhysicalPrimary.OriginalSelectedPrimaryStrain.StrainTransfer.NativeContext
public import JanetCartan.Iteration.PhysicalPrimary.OriginalSelectedPrimaryStrain.Node.MetricIdentity.NativeProof
import all JanetCartan.Iteration.PhysicalPrimary.OriginalSelectedPrimaryStrain.Node.MetricIdentity.NativeStatement

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

/-! Native source parameters for the original paired-source node deduction.
Only the existing numeric frame tolerance may occur in its intermediate
proof; the selected application supplies it from OriginalBareScale
(`main:eq:primary-strain`). -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true
set_option Elab.async false
open scoped ContDiff Matrix.Norms.Frobenius JanetCartan.TensorFrobenius

public meta section
namespace JanetCartan.PhysicalPrimary.OriginalSelectedPrimaryStrain.NodeUniformTransfer.NativeTemplate
open Lean Meta
open JanetCartan.PhysicalPrimary.OriginalSelectedPrimaryStrain
open NodeUniformTransfer.Template

def rho (source : Array Expr) : MetaM Expr := do
  let R := app ``JanetCartan.historyScale
    #[source[44]!,mkConst ``JanetCartan.growthExponent,source[46]!]
  mkAppM ``HPow.hPow #[R,mkConst ``JanetCartan.carrierExponent]

/-- The original aggregate's own node premise, before selected data substitution. -/
def requirement (sourceArgs : Array Expr) (q C hC : Expr) : MetaM Expr :=
  withLocalDeclNoLocalInstanceUpdate `δ .default (mkConst ``Real) fun δ => do
    let hδType ← mkAppM ``LE.le #[← mkNumeral (mkConst ``Real) 0,δ]
    withLocalDeclNoLocalInstanceUpdate `hδ .default hδType fun hδ => do
      let source := sourceArgs[:52].toArray
      let args := source[:44].toArray ++ #[C,hC,q] ++ source[44:].toArray ++ #[δ,hδ]
      let type ← FamilyTemplate.resultAt
        `JanetCartan.PhysicalPrimary.OriginalSampledPhysicalProfiles.selectedSourcePrimary_strain_of_complex_strain args
      let .forallE _ nodeType _ _ := type.consumeMData |
        throwError "native node transfer: original aggregate premise changed"
      let .forallE _ sampleType body _ := (← whnf nodeType).consumeMData |
        throwError "native node transfer: original sample binder changed"
      unless ← isDefEq sampleType (← inferType sourceArgs[52]!) do
        throwError "native node transfer: different original sample"
      let target := body.instantiate1 sourceArgs[52]!
      if (target.find? (fun e => e == δ || e == hδ)).isSome then
        throwError "native node transfer: amplitude escaped into node premise"
      return target

/-- Retain the native paired hypothesis or the native exact aggregate node target. -/
def publishStatement (node : Bool) : MetaM Unit := do
  StrainTransfer.NativeContext.withSource fun c => do
    let source := c.params[:53].toArray
    withLocalDeclNoLocalInstanceUpdate `accuracy .default (mkConst ``Nat) fun q =>
      withLocalDeclNoLocalInstanceUpdate `C .default (mkConst ``Real) fun C => do
        let p := source ++ #[q,C]
        unless p.size == 55 do throwError "native node transfer: source53/q/C boundary changed"
        if node then
          let nonneg ← mkAppM ``LE.le #[← mkNumeral (mkConst ``Real) 0,C]
          withLocalDeclNoLocalInstanceUpdate `hC .default nonneg fun hC => do
            let n := mkApp (mkConst ``Nat.succ) source[0]!
            let S := app ``JanetCartan.UniformStep.projectedStressResidualConstant #[n,source[1]!]
            let cost ← mkAppM ``HMul.hMul #[S,← mkAppM ``HAdd.hAdd #[C,C]]
            let hCost := app (root ++ `node_coefficient_nonneg) #[n,source[1]!,C,hC]
            save `native_node_strain_statement p (← requirement source q cost hCost) (mkSort .zero) true
        else
          let comparison := app (transferRoot ++ `native_node_strain_le_discrepancies) source
          forallBoundedTelescope (← inferType comparison) (some 1) fun frame atPoint => do
            unless frame.size == 1 do throwError "native node transfer: frame boundary changed"
            forallBoundedTelescope atPoint (some 2) fun point _ => do
              let quad := c.params[53]!
              let value := mkApp (app (sourceRoot ++ `discrepancy) (source.push quad)) point[0]!
              let norm ← mkAppM ``Norm.norm #[value]
              let price ← mkAppM ``HMul.hMul #[C,← decayAt (← rho source) q]
              let bound ← mkAppM ``LE.le #[norm,price]
              let target ← mkForallFVars #[quad] (← mkForallFVars point bound)
              save `native_paired_discrepancy_bound p target (mkSort .zero) true

/-- Compose the native transfer with the actual native metric identity and two source bounds. -/
def publishProof : MetaM Unit := do
  StrainTransfer.NativeContext.withSource fun c => do
    let source := c.params[:53].toArray
    withLocalDeclNoLocalInstanceUpdate `accuracy .default (mkConst ``Nat) fun q =>
      withLocalDeclNoLocalInstanceUpdate `C .default (mkConst ``Real) fun C => do
        let nonneg ← mkAppM ``LE.le #[← mkNumeral (mkConst ``Real) 0,C]
        withLocalDeclNoLocalInstanceUpdate `hC .default nonneg fun hC => do
          let comparison := app (transferRoot ++ `native_node_strain_le_discrepancies) source
          forallBoundedTelescope (← inferType comparison) (some 1) fun frame _ => do
            unless frame.size == 1 do throwError "native node transfer: frame boundary changed"
            let paired := app (root ++ `native_paired_discrepancy_bound) (source ++ #[q,C])
            withLocalDeclNoLocalInstanceUpdate `hPaired .default paired fun hPaired => do
              let named := app (root ++ `native_node_strain_statement) (source ++ #[q,C])
              let n := mkApp (mkConst ``Nat.succ) source[0]!
              let S := app ``JanetCartan.UniformStep.projectedStressResidualConstant #[n,source[1]!]
              let hS ← mkAppM ``le_of_lt
                #[app ``JanetCartan.UniformStep.projectedStressResidualConstant_pos #[n,source[1]!]]
              forallBoundedTelescope (← bodyAt named) (some 2) fun point expected => do
                let originalPoint := #[point[0]!,← ProofTemplate.originalCoreMembership point]
                let he := mkAppN comparison (frame ++ originalPoint)
                let ha := mkAppN hPaired (#[mkConst ``Bool.false] ++ originalPoint)
                let hb := mkAppN hPaired (#[mkConst ``Bool.true] ++ originalPoint)
                let ta ← inferType ha
                let tb ← inferType hb
                let saved ← inferType he
                unless saved.isAppOfArity (transferRoot ++ `native_node_strain_le_discrepancies_statement) 56 do
                  throwError "native node transfer: exact native comparison changed"
                let te ← bodyAt saved
                unless expected.isAppOfArity ``LE.le 4 && te.isAppOfArity ``LE.le 4 &&
                    ta.isAppOfArity ``LE.le 4 && tb.isAppOfArity ``LE.le 4 do
                  throwError "native node transfer: original inequalities changed"
                let selectedBound := app ``both_quadrature_bounds
                  #[te.getAppArgs[2]!,ta.getAppArgs[2]!,tb.getAppArgs[2]!,S,C,
                    ← decayAt (← rho source) q,hS,he,ha,hb]
                let tensorEq := app (primaryRoot ++ `Node.native_metric_tensor_eq) (source.push point[0]!)
                let tensorType ← bodyAt (← inferType tensorEq)
                let leftNorm := expected.getAppArgs[2]!
                let rightNorm := te.getAppArgs[2]!
                unless tensorType.isAppOfArity ``Eq 3 && leftNorm.isAppOfArity ``Norm.norm 3 &&
                    rightNorm.isAppOfArity ``Norm.norm 3 &&
                    tensorType.getAppArgs[1]! == leftNorm.getAppArgs[2]! &&
                    tensorType.getAppArgs[2]! == rightNorm.getAppArgs[2]! do
                  throwError "native node transfer: different actual node tensors"
                let normFn ← withLocalDeclNoLocalInstanceUpdate `tensor .default
                    tensorType.getAppArgs[0]! fun tensor =>
                  mkLambdaFVars #[tensor] (mkAppN rightNorm.getAppFn (rightNorm.getAppArgs.set! 2 tensor))
                let proof ← mkAppM ``le_of_eq_of_le #[← mkAppM ``congrArg #[normFn,tensorEq],selectedBound]
                let p := source ++ #[q,C,hC,frame[0]!,hPaired]
                unless p.size == 58 do throwError "native node transfer: extra analytic premise entered"
                save `native_node_of_paired_discrepancy p (← mkLambdaFVars point proof) named false

end JanetCartan.PhysicalPrimary.OriginalSelectedPrimaryStrain.NodeUniformTransfer.NativeTemplate
end

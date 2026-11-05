module

public meta import JanetCartan.Iteration.PhysicalPrimary.OriginalSelectedPrimaryStrain.FamilyTemplate
public import JanetCartan.Iteration.PhysicalPrimary.OriginalSelectedPrimaryStrain.AssemblyBasic
import all JanetCartan.Iteration.PhysicalBackground.CanonicalDensity
import all JanetCartan.Iteration.PhysicalMean.OriginalCanonicalMomentAdmissionTemplate
import all JanetCartan.Iteration.PhysicalSampling.OriginalPositiveEventApplication
import all JanetCartan.Iteration.PhysicalSampling.OriginalNativeInitialEventApplication
import all JanetCartan.Iteration.PhysicalSampling.OriginalNativeGradedEventApplication
import all JanetCartan.Iteration.PhysicalSampling.OriginalNativeSourceRowsApplication
public meta import Lean

/-! # Actual primary-node strain at arbitrary accuracy

Apply the fixed source discrepancy price to both labels of the SAME original
sample. The actual tensor/PDE transfer reconstructs its full complex strain.
The cost is fixed at selected33+N+accuracy before every history or target.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true
set_option Elab.async false

public meta section
namespace JanetCartan.PhysicalPrimary.OriginalSelectedPrimaryStrain.FamilyTemplate

open Lean Meta Elab Command

private def selectedNodeInequality (type : Expr) : MetaM Expr := do
  if type.isAppOfArity ``LE.le 4 then return type
  let mut result := type
  for key in #[
      `JanetCartan.PhysicalPrimary.OriginalSelectedPrimaryStrain.StrainTransfer.selected_node_strain_le_discrepancies_statement,
      `JanetCartan.PhysicalPrimary.OriginalSelectedPrimaryStrain.StrainTransfer.native_node_strain_le_discrepancies_statement] do
    unless result.isAppOfArity key 56 do
      throwError "actual primary node: exact selected/native statement head changed"
    let ci ← getConstInfo key
    let some value := ci.value? (allowOpaque := true) |
      throwError "actual primary node: exact selected/native statement is unavailable"
    result := ((value.instantiateLevelParams ci.levelParams
      result.getAppFn.constLevels!).beta result.getAppArgs).headBeta
  return result

elab "bound_actual_primary_node " mode:num : command => liftTermElabM do
  unless mode.getNat ≤ 3 do throwError "actual primary node: unknown mode"
  DataTemplate.withData fun d =>
    withLocalDeclNoLocalInstanceUpdate `accuracy .default (mkConst ``Nat) fun q => do
      let hOpType ← mkAppM ``LE.le
        #[app `JanetCartan.PhysicalPrimary.OriginalSelectedPrimaryStrain.Sop d.selected[:33].toArray,d.native[44]!]
      withLocalDeclNoLocalInstanceUpdate `hOp .default hOpType fun hOp => do
        let fixed := d.fixed.push q
        let n := mkApp (mkConst ``Nat.succ) d.native[0]!
        let C := app (root ++ `Cdiscrepancy) fixed
        let hC := app (root ++ `Cdiscrepancy_nonneg) fixed
        let S := app ``JanetCartan.UniformStep.projectedStressResidualConstant #[n,d.native[1]!]
        let hS ← mkAppM ``le_of_lt
          #[app ``JanetCartan.UniformStep.projectedStressResidualConstant_pos #[n,d.native[1]!]]
        if mode.getNat == 0 then
          let value ← mkAppM ``HMul.hMul #[S,← mkAppM ``HAdd.hAdd #[C,C]]
          save `Cnode fixed value (← inferType value) true
          return
        if mode.getNat == 1 then
          let proof ← mkAppM ``mul_nonneg #[hS,← mkAppM ``add_nonneg #[hC,hC]]
          let target ← mkAppM ``LE.le #[← mkNumeral (mkConst ``Real) 0,app (root ++ `Cnode) fixed]
          save `Cnode_nonneg fixed proof target
          return
        let comparison := app
          `JanetCartan.PhysicalPrimary.OriginalSelectedPrimaryStrain.StrainTransfer.selected_node_strain_le_discrepancies
          d.args
        forallBoundedTelescope (← inferType comparison) (some 2) fun point _ => do
          unless point.size == 2 do throwError "actual primary node: original closed-core point changed"
          let label (q : Bool) := app `JanetCartan.PhysicalPrimary.OriginalSelectedPrimaryStrain.observedLabel
            (d.profileArgs ++ #[mkConst (if q then ``Bool.true else ``Bool.false),hOp])
          let he := mkAppN comparison point
          let ha := mkAppN (app (root ++ `discrepancy_bound) fixed) (#[label false] ++ point)
          let hb := mkAppN (app (root ++ `discrepancy_bound) fixed) (#[label true] ++ point)
          let ta ← inferType ha
          let tb ← inferType hb
          let te ← selectedNodeInequality (← inferType he)
          unless ta.isAppOfArity ``LE.le 4 && tb.isAppOfArity ``LE.le 4 && te.isAppOfArity ``LE.le 4 do
            throwError "actual primary node: strain/discrepancy inequalities changed"
          let rhs := ta.getAppArgs[3]!
          unless rhs.isAppOfArity ``HMul.hMul 6 do
            throwError "actual primary node: original frequency decay disappeared"
          let decay := rhs.getAppArgs[5]!
          let proof := app ``both_quadrature_bounds
            #[te.getAppArgs[2]!,ta.getAppArgs[2]!,tb.getAppArgs[2]!,S,C,decay,hS,he,ha,hb]
          let bound ← mkAppM ``HMul.hMul #[app (root ++ `Cnode) fixed,decay]
          let target := mkAppN te.getAppFn (te.getAppArgs.set! 3 bound)
          let p := d.selected ++ #[d.hAux,hOp,d.steps,q,d.sample]
          if mode.getNat == 3 then
            save `node_strain_statement p (← mkForallFVars point target) (mkSort .zero) true
            setReducibilityStatus (root ++ `node_strain_statement) .reducible
          else
            save `node_strain_bound p (← mkLambdaFVars point proof)
              (app (root ++ `node_strain_statement) p)
end JanetCartan.PhysicalPrimary.OriginalSelectedPrimaryStrain.FamilyTemplate
end


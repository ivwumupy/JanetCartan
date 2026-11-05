module

public meta import JanetCartan.Iteration.PhysicalPrimary.OriginalSelectedPrimaryStrain.Node.UniformTransfer.Template
import all JanetCartan.Iteration.PhysicalPrimary.OriginalSelectedPrimaryStrain.Node.UniformTransfer.Template
import all JanetCartan.Iteration.PhysicalPrimary.OriginalSelectedPrimaryStrain.Family.Inputs
import all JanetCartan.Iteration.PhysicalPrimary.OriginalSelectedPrimaryStrain.ObservedLabels
import all JanetCartan.Iteration.PhysicalPrimary.OriginalSelectedPrimaryStrain.Labels
import all JanetCartan.Iteration.PhysicalPrimary.OriginalSelectedPrimaryStrain.SourceData
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

/-! Exact admitted-label source and carrier identities used to specialize the
full observed-family discrepancy bound (`main:eq:primary-strain`). -/

public meta section
namespace JanetCartan.PhysicalPrimary.OriginalSelectedPrimaryStrain.NodeUniformTransfer.IdentityTemplate
open Lean Meta
open JanetCartan.PhysicalPrimary.OriginalSelectedPrimaryStrain
open NodeUniformTransfer.Template

def retainIdentity (frequency statement : Bool) : MetaM Unit := do
  let statementKey := if frequency then `admitted_frequency_statement else `admitted_discrepancy_statement
  let proofKey := if frequency then `admitted_frequency_eq else `admitted_discrepancy_eq
  if statement then
    withOperator fun d hOp =>
      withLocalDeclNoLocalInstanceUpdate `imaginary .default (mkConst ``Bool) fun quad => do
        let p := d.profileArgs ++ #[quad,hOp]
        unless p.size == 57 do throwError "node uniform transfer: exact admitted label boundary changed"
        let label := labelAt d quad hOp
        let lhs := app (familyRoot ++ (if frequency then `frequency else `discrepancy)) (d.fixed.push label)
        let rhs ← if frequency then rhoAt d else
          pure (app (sourceRoot ++ `discrepancy) (d.sourceArgs.push quad))
        let alpha ← inferType rhs
        let target := mkAppN (mkConst ``Eq [.succ .zero]) #[alpha,lhs,rhs]
        save statementKey p target (mkSort .zero) true
  else
    let statementName := root ++ statementKey
    openRaw 57 (← getConstInfo statementName).type fun p => do
      let eq ← bodyAt (app statementName p)
      unless eq.isAppOfArity ``Eq 3 do throwError "node uniform transfer: exact equality changed"
      let a := eq.getAppArgs
      let proof := mkAppN (mkConst ``Eq.refl eq.getAppFn.constLevels!) #[a[0]!,a[2]!]
      save proofKey p proof (app statementName p) false


end JanetCartan.PhysicalPrimary.OriginalSelectedPrimaryStrain.NodeUniformTransfer.IdentityTemplate
end

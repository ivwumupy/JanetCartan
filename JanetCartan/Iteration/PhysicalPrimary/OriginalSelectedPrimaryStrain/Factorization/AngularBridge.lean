module

public import JanetCartan.Iteration.PhysicalPrimary.OriginalSelectedPrimaryStrain.Factorization.AngularStatement
public import JanetCartan.Iteration.PhysicalPrimary.OriginalSelectedPrimaryStrain.Factorization.AngularBridge.Native
public import JanetCartan.Iteration.PhysicalPrimary.OriginalSelectedPrimaryStrain.Factorization.AngularBridge.Field
public import JanetCartan.Iteration.PhysicalPrimary.OriginalSelectedPrimaryStrain.Factorization.AngularBridge.Sum
import all JanetCartan.Iteration.PhysicalPrimary.OriginalSelectedPrimaryStrain.Factorization.AngularTemplate
import all JanetCartan.Iteration.PhysicalPrimary.OriginalRawPrimaryIntegral
import all JanetCartan.Iteration.PhysicalMean.OriginalMeanQuadraticCoordinates
import all JanetCartan.Iteration.PhysicalSampling.OriginalPositiveEventApplication
import all JanetCartan.Iteration.PhysicalSampling.OriginalNativeGradedEventApplication
import all JanetCartan.Iteration.PhysicalSampling.OriginalNativeInitialEventApplication
import all JanetCartan.Iteration.PhysicalSampling.OriginalNativeSourceRowsApplication

/-!
# The original actual raw angular derivative

The native derivative is transported through explicit equalities of the same
raw field, ordinary phase, single scalar mask and forward amplitude. The
conclusion is exactly the existing `Actual.unprefixed_forward_statement`;
no source estimate, response identity or success premise is added. This is
the missing raw-angular input to the primary factorization
(`main:eq:primary-strain`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true
set_option Elab.async false

public meta section
namespace JanetCartan.PhysicalPrimary.OriginalSelectedPrimaryStrain.Factorization.AngularBridge.Template

open Lean Meta Elab Command
open OriginalRawAngularActualApplication

elab "close_original_actual_raw_angular_forward" : command => liftTermElabM do
  withStoredTelescope (actual ++ `unprefixed_forward_statement) 56 fun all _ => do
    let nativeInfo ← getConstInfo (root ++ `native_forward_statement)
    let nativeEq := (nativeInfo.value! (allowOpaque := true)).beta all
    unless nativeEq.isAppOfArity ``Eq 3 do
      throwError "raw angular bridge: the cached native derivative changed"
    let lhs := nativeEq.getAppArgs[1]!
    let rhs := nativeEq.getAppArgs[2]!
    let hfield := app (root ++ `raw_field_eq_native) all[:54].toArray
    let fieldEq ← storedType (root ++ `raw_field_eq_native) all[:54].toArray
    let raw := fieldEq.getAppArgs[2]!
    unless (lhs.find? (· == raw)).isSome do
      throwError "raw angular bridge: the cached derivative changed its original field"
    let context ← withLocalDeclD `rawField (← inferType raw) fun field =>
      mkLambdaFVars #[field] (lhs.replace fun e => if e == raw then some field else none)
    let left ← exactCongr context hfield
    let right := app (root ++ `native_rhs_eq_actual_sum) all[:55].toArray
    let middle := app (root ++ `native_forward) all
    let lt ← inferType left
    let rt ← storedEquality (root ++ `native_rhs_eq_actual_sum) all[:55].toArray
    let a := lt.getAppArgs
    let last := rt.getAppArgs[2]!
    let trans := mkConst ``Eq.trans lt.getAppFn.constLevels!
    let tail := mkAppN trans #[a[0]!,lhs,rhs,last,middle,right]
    let proof := mkAppN trans #[a[0]!,a[1]!,lhs,last,left,tail]
    publish `unprefixed_forward all proof (app (actual ++ `unprefixed_forward_statement) all)

close_original_actual_raw_angular_forward

end JanetCartan.PhysicalPrimary.OriginalSelectedPrimaryStrain.Factorization.AngularBridge.Template
end

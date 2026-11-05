module

public meta import JanetCartan.Iteration.PhysicalPrimary.OriginalSelectedPrimaryStrain.FamilyTemplate
public import JanetCartan.Iteration.PhysicalPrimary.OriginalSelectedPrimaryStrain.SourceResidual.GraphSmooth
public import JanetCartan.Iteration.PhysicalPrimary.OriginalSelectedPrimaryStrain.Discrepancy.Transport
import all JanetCartan.Iteration.PhysicalBackground.CanonicalDensity
import all JanetCartan.Iteration.PhysicalMean.OriginalCanonicalMomentAdmissionTemplate
import all JanetCartan.Iteration.PhysicalSampling.OriginalPositiveEventApplication
import all JanetCartan.Iteration.PhysicalSampling.OriginalNativeInitialEventApplication
import all JanetCartan.Iteration.PhysicalSampling.OriginalNativeGradedEventApplication
import all JanetCartan.Iteration.PhysicalSampling.OriginalNativeSourceRowsApplication
public meta import Lean

/-! # Actual arbitrary-order primary source discrepancy

The original observed chain and uncut inverse remainder are instantiated on
the entire primary label family. All six source inputs are genuine producers.
The fixed discrepancy price precedes every history, target and sample, and
applies to the existing smooth representative on the closed original half
core (`main:eq:primary-strain`, `app:ch_regular:eq:inverse-remainder`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true
set_option Elab.async false

public meta section
namespace JanetCartan.PhysicalPrimary.OriginalSelectedPrimaryStrain.FamilyTemplate

open Lean Meta Elab Command

private def sourceIdentityType (key : Name) (p : Array Expr) : MetaM Expr := do
  let target ← resultAt key p
  if target.isAppOfArity ``Eq 3 then return target
  unless target.isAppOfArity (root ++ `ResidualIdentity.observed_discrepancy_statement) 35 ||
      target.isAppOfArity (root ++ `ResidualIdentity.history_frequency_statement) 35 do
    throwError "actual primary discrepancy: original identity statement changed"
  let ci ← getConstInfo target.getAppFn.constName!
  let some value := ci.value? (allowOpaque := true) |
    throwError "actual primary discrepancy: original identity statement is unavailable"
  let result := ((value.instantiateLevelParams ci.levelParams
    target.getAppFn.constLevels!).beta target.getAppArgs).headBeta
  unless result.isAppOfArity ``Eq 3 do
    throwError "actual primary discrepancy: original identity statement is not an equality"
  return result

elab "bound_actual_primary_discrepancy " mode:num : command => liftTermElabM do
  unless mode.getNat ≤ 5 do throwError "actual primary discrepancy: unknown mode"
  withFamily fun c =>
    withLocalDeclNoLocalInstanceUpdate `accuracy .default (mkConst ``Nat) fun q => do
      let fixed := c.fixed.push q
      let existence := app (root ++ `discrepancy_exists) fixed
      if mode.getNat == 1 then
        let value ← mkAppM ``Classical.choose #[existence]
        save `Cdiscrepancy fixed value (← inferType value) true
        return
      if mode.getNat == 2 || mode.getNat == 3 || mode.getNat == 5 then
        let spec ← mkAppM ``Classical.choose_spec #[existence]
        let proof := if mode.getNat == 2 then Expr.proj ``And 0 spec else Expr.proj ``And 1 spec
        let value ← mkAppM ``Classical.choose #[existence]
        let target := (← inferType proof).replace fun e =>
          if e == value then some (app (root ++ `Cdiscrepancy) fixed) else none
        if mode.getNat == 5 then
          save `discrepancy_bound_statement fixed target (mkSort .zero) true
          setReducibilityStatus (root ++ `discrepancy_bound_statement) .reducible
        else if mode.getNat == 3 then
          save `discrepancy_bound fixed proof
            (app (root ++ `discrepancy_bound_statement) fixed)
        else
          save `Cdiscrepancy_nonneg fixed proof target
        return
      let qr ← mkAppOptM ``Nat.cast #[some (mkConst ``Real),none,some q]
      let proof := app `JanetCartan.PhysicalPrimary.OriginalSelectedPrimaryStrain.SourceResidual.smooth_discrepancy_cNorm
        (c.graph[:36].toArray ++ #[c.labels,c.field `historyMap,c.field `smoothInput,
          c.field `support,c.field `source_polynomial,c.field `first_mask,c.field `CN,
          c.field `CN_nonneg,c.field `negative_moments,mkNatLit 0,qr])
      let type ← inferType proof
      let some K := type.find? (·.isAppOf ``Metric.closedBall) |
        throwError "actual primary discrepancy: original closed core disappeared"
      let ka := K.getAppArgs
      let smooth ← c.family (app (source ++ `discrepancy_smooth) c.sourceArgs)
      let n := mkApp (mkConst ``Nat.succ) c.data.native[0]!
      let identity ← sourceIdentityType (root ++ `observed_discrepancy_eq)
        (c.fixed.push c.label)
      let frequencyIdentity ← sourceIdentityType (root ++ `history_frequency_eq)
        (c.fixed.push c.label)
      unless identity.isAppOfArity ``Eq 3 && frequencyIdentity.isAppOfArity ``Eq 3 do
        throwError "actual primary discrepancy: exact source/frequency identities changed"
      let observed ← c.family identity.getAppArgs[1]!
      let observedFrequency ← c.family frequencyIdentity.getAppArgs[1]!
      let point := mkAppN (mkConst
        ``JanetCartan.PhysicalPrimary.OriginalSelectedPrimaryStrain.point_of_cnorm_of_source_identities [.zero])
        #[n,c.labels,ka[ka.size-2]!,ka.back!,observedFrequency,c.field `frequency,
          observed,c.field `discrepancy,smooth,qr,c.field `observed_discrepancy_eq,
          c.field `history_frequency_eq,proof]
      if mode.getNat == 4 then
        save `discrepancy_exists_statement fixed (← inferType point) (mkSort .zero) true
        setReducibilityStatus (root ++ `discrepancy_exists_statement) .reducible
      else
        save `discrepancy_exists fixed point
          (app (root ++ `discrepancy_exists_statement) fixed)

end JanetCartan.PhysicalPrimary.OriginalSelectedPrimaryStrain.FamilyTemplate
end


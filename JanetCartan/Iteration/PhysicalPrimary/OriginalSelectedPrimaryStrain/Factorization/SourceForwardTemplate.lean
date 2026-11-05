module
public import JanetCartan.Iteration.PhysicalPrimary.OriginalSelectedPrimaryStrain.Factorization.SourceData
import all JanetCartan.Iteration.PhysicalPrimary.OriginalSelectedPrimaryStrain.Factorization.SourceTemplate
import all JanetCartan.Iteration.PhysicalPrimary.OriginalSelectedPrimaryStrain.Factorization.AngularTemplate
import all JanetCartan.Iteration.PhysicalSampling.OriginalPositiveEventApplication
import all JanetCartan.Iteration.PhysicalSampling.OriginalNativeInitialEventApplication
import all JanetCartan.Iteration.PhysicalSampling.OriginalNativeGradedEventApplication
import all JanetCartan.Iteration.PhysicalSampling.OriginalNativeSourceRowsApplication
import all JanetCartan.Iteration.PhysicalMean.OriginalCanonicalDerivativeTemplate
/-! Original source-input substitution into the exact raw prefix formula.
The implication is checked independently of its producer; the actual source
endpoint supplies the completed prefixed identity and has no additional premise
(main:eq:primary-strain). -/
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true
set_option Elab.async false
public meta section
open Lean Meta Elab Command
namespace JanetCartan.PhysicalPrimary.OriginalSelectedPrimaryStrain.Factorization.SourceTemplate

elab "derive_original_raw_source_from_prefix " mode:num : command => liftTermElabM do
  unless mode.getNat < 3 do throwError "raw source from prefix: unknown stage"
  withSource fun d => do
    let inputArgs := d.actualArgs ++ #[d.primitive[52]!,d.refinedInput]
    if mode.getNat == 2 then
      let statement := app (root ++ `observed_raw_angular_statement) d.params
      forallBoundedTelescope (← typeAt statement) (some 2) fun point _ => do
        unless point.size == 2 do throwError "raw source from prefix: original source tail changed"
        let all := d.params ++ point
        let forward := app (angular ++ `prefixed_forward) (inputArgs ++ point)
        let proof := app (root ++ `observed_raw_angular_of_prefixed) (all.push forward)
        save `observed_raw_angular_eq_source all proof
          (app (root ++ `observed_raw_angular_statement) all)
      return
    let stem := app (angular ++ `prefixed_forward_statement) inputArgs
    forallBoundedTelescope (← typeAt stem) (some 2) fun point _ => do
      unless point.size == 2 do throwError "raw source from prefix: original source point/chart changed"
      let all := d.params ++ point
      let prefixed := mkAppN stem point
      withLocalDeclD `hPrefixed prefixed fun forward => do
        let grouped := app `JanetCartan.PhysicalPrimary.OriginalRawGroupedRealization.raw_annular_sum_eq_field
          (d.params.push point[0]!)
        let ft ← bodyAt prefixed
        let gt ← typeAt grouped
        unless ft.isAppOfArity ``Eq 3 && gt.isAppOfArity ``Eq 3 do
          throwError "raw source from prefix: original full annular equalities changed"
        let a := ft.getAppArgs
        let b := gt.getAppArgs
        let proof := mkAppN (mkConst ``Eq.trans ft.getAppFn.constLevels!)
          #[a[0]!,a[1]!,a[2]!,b[2]!,forward,grouped]
        let lhs ← renameDerivative a[1]! d.angularField
        let rhs := mkApp (app (source ++ `field) d.params) point[0]!
        let target ← mkEq lhs rhs
        if mode.getNat == 0 then
          save `observed_raw_angular_statement all target (mkSort .zero) true
        else
          save `observed_raw_angular_of_prefixed (all.push forward) proof
            (app (root ++ `observed_raw_angular_statement) all)
          addDocStringCore (root ++ `observed_raw_angular_of_prefixed)
            "Conditional substitution of the SAME original unweighted adjoint/source into the full prefixed raw annular identity. The actual observed_raw_angular_eq_source supplies the completed original prefix producer; no raw/corrected-G equality or source-success bound is assumed (main:eq:primary-strain)."

end JanetCartan.PhysicalPrimary.OriginalSelectedPrimaryStrain.Factorization.SourceTemplate
end
